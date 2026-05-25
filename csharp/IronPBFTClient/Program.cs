using System;
using System.Diagnostics;
using System.IO;
using System.Net;
using System.Net.Sockets;
using System.Threading;

namespace IronPBFTClient
{
    /// <summary>
    /// Fire-and-forget UDP client for the PBFT protocol.
    ///
    /// PBFT has no client response message in this implementation — the
    /// primary silently accepts ClientRequest messages and drives them
    /// through the pre-prepare/prepare/commit pipeline.
    /// Throughput is measured server-side via [METRICS] output on the
    /// primary's seq_num increments.
    ///
    /// This client sends ClientRequest messages as fast as possible to
    /// drive load. It counts sends per second as an injection-rate metric,
    /// but the true committed throughput comes from server [METRICS].
    ///
    /// Wire format (little-endian u64 fields):
    ///   ClientRequest: [TAG=4][digest] = 16 bytes
    /// </summary>
    class Program
    {
        private const ulong TAG_CLIENT_REQUEST = 4;

        static void Usage()
        {
            Console.Write(@"
Usage:  dotnet IronPBFTClient.dll [key=value]...

Allowed keys:
  ip         - IP address of primary server (default 127.0.0.1)
  port       - Port of primary server (default 4001)
  nthreads   - Number of client threads (default 1)
  duration   - Duration in seconds (default 30)

Wire format (little-endian u64 fields, 16 bytes):
  Send: [TAG=4][digest]

Note: PBFT has no client reply in this implementation. Throughput is
measured server-side via [METRICS] output (seq_num increments/s).
This client reports injection rate (sends/s) for reference.
");
        }

        static void Main(string[] args)
        {
            IPAddress ip = IPAddress.Parse("127.0.0.1");
            int port = 4001;
            int nthreads = 1;
            int duration = 30;

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
                        case "ip": ip = IPAddress.Parse(value); break;
                        case "port": port = Convert.ToInt32(value); break;
                        case "nthreads": nthreads = Convert.ToInt32(value); break;
                        case "duration": duration = Convert.ToInt32(value); break;
                        default:
                            Console.WriteLine("Invalid argument {0}", arg);
                            Usage();
                            return;
                    }
                }
                catch (Exception e)
                {
                    Console.WriteLine("Invalid value for key {0}: {1}", key, e.Message);
                    Usage();
                    return;
                }
            }

            var endpoint = new IPEndPoint(ip, port);
            long[] sendCounts = new long[nthreads];

            Console.Error.WriteLine(
                "PBFT client: {0} thread(s), {1}s, target={2}",
                nthreads, duration, endpoint);
            Console.WriteLine("[[READY]]");

            var threads = new Thread[nthreads];
            var running = new int[] { 1 }; // shared stop flag

            for (int i = 0; i < nthreads; i++)
            {
                int threadId = i;
                int threadPort = 8000 + i;
                threads[i] = new Thread(() =>
                {
                    Thread.Sleep(1000); // brief startup delay
                    var udp = new UdpClient(threadPort);
                    ulong counter = 0;
                    while (Volatile.Read(ref running[0]) == 1)
                    {
                        counter++;
                        byte[] pkt = EncodeClientRequest(counter);
                        udp.Send(pkt, pkt.Length, endpoint);
                        Volatile.Write(ref sendCounts[threadId], (long)counter);
                    }
                    udp.Close();
                });
                threads[i].Start();
            }

            Thread.Sleep(duration * 1000);
            Volatile.Write(ref running[0], 0);

            long totalSends = 0;
            for (int i = 0; i < nthreads; i++)
            {
                threads[i].Join(2000);
                long sends = Volatile.Read(ref sendCounts[i]);
                totalSends += sends;
                Console.WriteLine("Thread {0}: {1} sends", i, sends);
            }

            // Subtract 1s startup delay
            double effectiveDuration = Math.Max(1, duration - 1);
            double sendRate = totalSends / effectiveDuration;
            Console.WriteLine(
                "injection_rate {0:F1} sends/sec (server [METRICS] shows committed throughput)",
                sendRate);
            Console.WriteLine("[[DONE]]");
        }

        private static byte[] EncodeClientRequest(ulong digest)
        {
            using (var ms = new MemoryStream(16))
            {
                WriteLE64(ms, TAG_CLIENT_REQUEST);
                WriteLE64(ms, digest);
                return ms.ToArray();
            }
        }

        private static void WriteLE64(MemoryStream ms, ulong value)
        {
            byte[] bytes = BitConverter.GetBytes(value);
            if (!BitConverter.IsLittleEndian)
            {
                Array.Reverse(bytes);
            }
            ms.Write(bytes, 0, bytes.Length);
        }
    }
}
