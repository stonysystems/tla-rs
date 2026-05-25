using System;
using System.Collections.Generic;
using System.Net;
using System.Threading;

namespace IronGenericClient
{
    class Program
    {
        static void Usage()
        {
            Console.Write(@"
Usage:  dotnet IronGenericClient.dll protocol=<name> [key=value]...

Required:
  protocol   - One of: raft, pb, pbft, epaxos

Optional:
  ip1..ipN   - IP addresses of servers (default 127.0.0.1)
  port1..portN - Ports of servers (default 4001..400N)
  nservers   - Number of servers (default 3; overridden by explicit ipN/portN)
  nthreads   - Number of client threads (default 1)
  duration   - Duration in seconds (default 30)
  clientport - Base port for client threads (default 7000)
  leader     - Server index to try first, 0-based (default: auto-discover)

Output:
  throughput <N> ops/sec | avg latency ms <X>
");
        }

        static void Main(string[] args)
        {
            string protocol = null;
            int nthreads = 1;
            int duration = 30;
            int clientPort = 7000;
            int leaderIdx = -1;
            int nservers = 3;

            // Collect explicit ip/port overrides
            var ipOverrides = new Dictionary<int, IPAddress>();
            var portOverrides = new Dictionary<int, int>();

            foreach (var arg in args)
            {
                var pos = arg.IndexOf("=");
                if (pos < 0)
                {
                    Console.WriteLine("Invalid argument: {0}", arg);
                    Usage();
                    return;
                }
                var key = arg.Substring(0, pos).ToLower();
                var value = arg.Substring(pos + 1);
                try
                {
                    if (key == "protocol") { protocol = value.ToLower(); }
                    else if (key == "nthreads") { nthreads = Convert.ToInt32(value); }
                    else if (key == "duration") { duration = Convert.ToInt32(value); }
                    else if (key == "clientport") { clientPort = Convert.ToInt32(value); }
                    else if (key == "leader") { leaderIdx = Convert.ToInt32(value); }
                    else if (key == "nservers") { nservers = Convert.ToInt32(value); }
                    else if (key.StartsWith("ip") && int.TryParse(key.Substring(2), out int ipIdx))
                    {
                        ipOverrides[ipIdx] = IPAddress.Parse(value);
                        if (ipIdx > nservers) nservers = ipIdx;
                    }
                    else if (key.StartsWith("port") && int.TryParse(key.Substring(4), out int portIdx))
                    {
                        portOverrides[portIdx] = Convert.ToInt32(value);
                        if (portIdx > nservers) nservers = portIdx;
                    }
                    else
                    {
                        Console.WriteLine("Unknown argument: {0}", arg);
                        Usage();
                        return;
                    }
                }
                catch (Exception e)
                {
                    Console.WriteLine("Invalid value for {0}: {1}", key, e.Message);
                    Usage();
                    return;
                }
            }

            if (protocol == null)
            {
                Console.WriteLine("Error: protocol=<name> is required.");
                Usage();
                return;
            }

            IProtocolAdapter adapter;
            switch (protocol)
            {
                case "raft": adapter = new RaftAdapter(); break;
                case "pb": case "primarybackup": adapter = new PBAdapter(); break;
                case "pbft": adapter = new PBFTAdapter(); break;
                case "epaxos": adapter = new EPaxosAdapter(); break;
                default:
                    Console.WriteLine("Unknown protocol: {0}", protocol);
                    Usage();
                    return;
            }

            // Build endpoint list
            var endpoints = new List<IPEndPoint>();
            for (int i = 1; i <= nservers; i++)
            {
                var ip = ipOverrides.ContainsKey(i)
                    ? ipOverrides[i]
                    : IPAddress.Parse("127.0.0.1");
                int port = portOverrides.ContainsKey(i) ? portOverrides[i] : 4000 + i;
                endpoints.Add(new IPEndPoint(ip, port));
            }

            int[] reqCounts = new int[nthreads];
            double[] latencySums = new double[nthreads];
            int[] sharedLeaderIdx = new int[] { leaderIdx };
            int[] running = new int[] { 1 };

            HiResTimer.Initialize();
            Console.Error.WriteLine("{0} client: {1} thread(s), {2}s, servers={3}",
                protocol.ToUpper(), nthreads, duration,
                string.Join(", ", endpoints));
            Console.WriteLine("[[READY]]");

            var threads = new Thread[nthreads];
            for (int i = 0; i < nthreads; i++)
            {
                int tid = i;
                int port = clientPort + i;
                var client = new SyncClient(adapter, endpoints, port);
                threads[i] = new Thread(() =>
                    client.Run(tid, reqCounts, latencySums, sharedLeaderIdx, running));
                threads[i].Start();
            }

            Thread.Sleep(duration * 1000);
            Volatile.Write(ref running[0], 0);

            int totalReqs = 0;
            double totalLatency = 0;
            for (int i = 0; i < nthreads; i++)
            {
                threads[i].Join(5000);
                totalReqs += reqCounts[i];
                totalLatency += latencySums[i];
                if (reqCounts[i] > 0)
                {
                    Console.WriteLine("Client {0} throughput {1} | avg latency ms {2:F2}",
                        i, reqCounts[i], latencySums[i] / reqCounts[i]);
                }
            }

            // Subtract 3s startup delay
            double effectiveDuration = Math.Max(1, duration - 4);
            double throughput = totalReqs / effectiveDuration;
            double avgLatency = totalReqs > 0 ? totalLatency / totalReqs : 0;

            Console.WriteLine("throughput {0:F1} ops/sec | avg latency ms {1:F2}",
                throughput, avgLatency);
            Console.WriteLine("[[DONE]]");
            Environment.Exit(0);
        }
    }
}
