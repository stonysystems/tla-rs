using System;
using System.Linq;
using System.Threading;
using System.IO;
using System.Net;
using System.Collections.Generic;
using System.Diagnostics;

namespace IronRaftClient
{
    class Program
    {
        static void Usage()
        {
            Console.Write(@"
Usage:  dotnet IronRaftClient.dll [key=value]...

Allowed keys:
  clientip   - IP address this client should bind to (default 127.0.0.1)
  clientport - Port this client should bind to (default 7000)
  ip1        - IP address of first Raft server (default 127.0.0.1)
  ip2        - IP address of second Raft server (default 127.0.0.1)
  ip3        - IP address of third Raft server (default 127.0.0.1)
  port1      - Port of first Raft server (default 4001)
  port2      - Port of second Raft server (default 4002)
  port3      - Port of third Raft server (default 4003)
  nthreads   - Number of client threads to run (default 1)
  duration   - Duration of experiment in seconds (default 60)
  initialseqno - First sequence number each thread uses (default 0)

Wire format (little-endian u64 fields, 32 bytes each):
  Send: [TAG=5][client_id][seq_no][value]
  Recv: [TAG=6][client_id][seq_no][success]
");
        }

        static void Main(string[] args)
        {
            int numThreads = 1;
            ulong duration = 60;
            IPAddress clientIp = IPAddress.Parse("127.0.0.1");
            IPAddress ip1 = IPAddress.Parse("127.0.0.1");
            IPAddress ip2 = IPAddress.Parse("127.0.0.1");
            IPAddress ip3 = IPAddress.Parse("127.0.0.1");
            int clientPort = 7000;
            int port1 = 4001;
            int port2 = 4002;
            int port3 = 4003;
            ulong initialSeqNo = 0;

            foreach (var arg in args)
            {
                var pos = arg.IndexOf("=");
                if (pos < 0)
                {
                    Console.WriteLine("Invalid argument {0}", arg);
                    Usage();
                    return;
                }
                var key = arg.Substring(0, pos).ToLower();
                var value = arg.Substring(pos + 1);
                try
                {
                    switch (key)
                    {
                        case "clientip": clientIp = IPAddress.Parse(value); break;
                        case "clientport": clientPort = Convert.ToInt32(value); break;
                        case "ip1": ip1 = IPAddress.Parse(value); break;
                        case "ip2": ip2 = IPAddress.Parse(value); break;
                        case "ip3": ip3 = IPAddress.Parse(value); break;
                        case "port1": port1 = Convert.ToInt32(value); break;
                        case "port2": port2 = Convert.ToInt32(value); break;
                        case "port3": port3 = Convert.ToInt32(value); break;
                        case "nthreads": numThreads = Convert.ToInt32(value); break;
                        case "duration": duration = Convert.ToUInt64(value); break;
                        case "initialseqno": initialSeqNo = Convert.ToUInt64(value); break;
                        default:
                            Console.WriteLine("Invalid argument {0}", arg);
                            Usage();
                            return;
                    }
                }
                catch (Exception e)
                {
                    Console.WriteLine("Invalid value {0} for key {1}: {2}", value, key, e.Message);
                    Usage();
                    return;
                }
            }

            var endpoints = new List<IPEndPoint>
            {
                new IPEndPoint(ip1, port1),
                new IPEndPoint(ip2, port2),
                new IPEndPoint(ip3, port3),
            };

            int[] reqCounts = new int[numThreads];
            double[] latencySums = new double[numThreads];

            HiResTimer.Initialize();
            Console.Error.WriteLine("Raft benchmark client starting {0} thread(s) for {1}s ...", numThreads, duration);
            Console.WriteLine("[[READY]]");

            TextWriter stdout = Console.Out;

            // Start benchmark threads
            var threads = new Thread[numThreads];
            for (int i = 0; i < numThreads; i++)
            {
                var p = new ClientParams
                {
                    Id = i,
                    Port = clientPort + i,
                    InitialSeqNo = initialSeqNo,
                    Endpoints = endpoints,
                    ReqCounts = reqCounts,
                    LatencySums = latencySums,
                };
                threads[i] = new Thread(Client.Run);
                threads[i].Start(p);
            }

            if (duration == 0)
            {
                // Run forever
                threads[0].Join();
            }
            else
            {
                Thread.Sleep((int)duration * 1000);
                stdout.WriteLine("[[DONE]]");
                stdout.Flush();

                int totalReqs = 0;
                double totalLatency = 0;

                for (int i = 0; i < numThreads; i++)
                {
                    int reqs = reqCounts[i];
                    double lat = latencySums[i];
                    totalReqs += reqs;
                    totalLatency += lat;
                    if (reqs > 0)
                    {
                        stdout.WriteLine("Client {0} throughput {1} | avg latency ms {2:F2}",
                            i, reqs, lat / reqs);
                    }
                }

                // Subtract startup delay (3s thread sleep + warmup)
                double effectiveDuration = Math.Max(1, (double)duration - 4);
                double throughput = totalReqs / effectiveDuration;
                double avgLatency = totalReqs > 0 ? totalLatency / totalReqs : 0;

                stdout.WriteLine("throughput {0:F1} ops/sec | avg latency ms {1:F2}", throughput, avgLatency);
                Environment.Exit(0);
            }
        }
    }

    public class HiResTimer
    {
        private static Stopwatch _stopWatch;

        public static long Ticks => _stopWatch.ElapsedTicks;

        public static void Initialize()
        {
            _stopWatch = Stopwatch.StartNew();
        }

        public static double TicksToMilliseconds(long ticks)
        {
            return ticks * 1000.0 / Stopwatch.Frequency;
        }
    }
}
