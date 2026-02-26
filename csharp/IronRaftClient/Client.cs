namespace IronRaftClient
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Net;
    using System.Net.Sockets;
    using System.Linq;

    /// <summary>
    /// Parameters passed to each benchmark thread.
    /// </summary>
    public struct ClientParams
    {
        public int Id;
        public int Port;
        public ulong InitialSeqNo;
        public List<IPEndPoint> Endpoints;
        public int[] ReqCounts;
        public double[] LatencySums;
    }

    /// <summary>
    /// Raft benchmark client. Sends ClientRequest messages (TAG=5) and waits
    /// for matching ClientResponse messages (TAG=6). Rotates between servers
    /// on timeout to discover the leader.
    ///
    /// Wire format (little-endian u64 fields):
    ///   ClientRequest:  [5][client_id][seq_no][value]  = 32 bytes
    ///   ClientResponse: [6][client_id][seq_no][success] = 32 bytes
    /// </summary>
    public class Client
    {
        private const ulong TAG_CLIENT_REQUEST = 5;
        private const ulong TAG_CLIENT_RESPONSE = 6;

        private UdpClient udpClient;
        private List<IPEndPoint> endpoints;
        private ulong clientId;

        public static void Run(object param)
        {
            System.Threading.Thread.Sleep(3000); // Stagger startup
            var p = (ClientParams)param;
            var client = new Client();
            client.Main(p.Id, p.Port, p.InitialSeqNo, p.Endpoints, p.ReqCounts, p.LatencySums);
        }

        private void Main(
            int id,
            int port,
            ulong initialSeqNo,
            List<IPEndPoint> endpoints,
            int[] reqCounts,
            double[] latencySums)
        {
            this.endpoints = endpoints;
            this.udpClient = new UdpClient(port);
            this.udpClient.Client.ReceiveTimeout = 1000; // 1-second timeout
            this.clientId = (ulong)port; // Use port as unique client ID

            int serverIdx = 0;

            for (ulong seqNo = initialSeqNo; ; seqNo++)
            {
                byte[] request = EncodeClientRequest(clientId, seqNo, seqNo); // value = seqNo

                var startTime = HiResTimer.Ticks;
                Send(request, endpoints[serverIdx]);

                bool receivedReply = false;
                while (!receivedReply)
                {
                    byte[] bytes;
                    try
                    {
                        IPEndPoint sender = null;
                        bytes = udpClient.Receive(ref sender);
                    }
                    catch (SocketException)
                    {
                        // Timeout: rotate to next server (leader discovery)
                        serverIdx = (serverIdx + 1) % endpoints.Count;
                        Send(request, endpoints[serverIdx]);
                        continue;
                    }

                    var endTime = HiResTimer.Ticks;

                    // Parse ClientResponse: [TAG=6][client_id][seq_no][success]
                    if (bytes.Length < 32)
                    {
                        Console.Error.WriteLine("Client {0}: unexpected packet length {1}", id, bytes.Length);
                        continue;
                    }

                    int offset = 0;
                    ulong tag = ReadLE64(bytes, ref offset);
                    if (tag != TAG_CLIENT_RESPONSE)
                    {
                        // Not a client response — ignore
                        continue;
                    }

                    ulong respClientId = ReadLE64(bytes, ref offset);
                    ulong respSeqNo = ReadLE64(bytes, ref offset);
                    ulong respSuccess = ReadLE64(bytes, ref offset);

                    if (respSeqNo != seqNo || respClientId != clientId)
                    {
                        // Stale or mismatched response — keep waiting
                        continue;
                    }

                    if (respSuccess == 0)
                    {
                        // Not leader: rotate to next server and retry
                        serverIdx = (serverIdx + 1) % endpoints.Count;
                        Send(request, endpoints[serverIdx]);
                        continue;
                    }

                    // Success!
                    receivedReply = true;
                    double latencyMs = HiResTimer.TicksToMilliseconds(endTime - startTime);
                    reqCounts[id] += 1;
                    latencySums[id] += latencyMs;
                }
            }
        }

        /// <summary>
        /// Encode a ClientRequest message: [TAG=5][client_id][seq_no][value]
        /// All fields are little-endian u64, total 32 bytes.
        /// </summary>
        private static byte[] EncodeClientRequest(ulong clientId, ulong seqNo, ulong value)
        {
            using (var ms = new MemoryStream(32))
            {
                WriteLE64(ms, TAG_CLIENT_REQUEST);
                WriteLE64(ms, clientId);
                WriteLE64(ms, seqNo);
                WriteLE64(ms, value);
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

        private static ulong ReadLE64(byte[] data, ref int offset)
        {
            byte[] extracted = data.Skip(offset).Take(8).ToArray();
            if (!BitConverter.IsLittleEndian)
            {
                Array.Reverse(extracted);
            }
            offset += 8;
            return BitConverter.ToUInt64(extracted, 0);
        }

        private void Send(byte[] data, IPEndPoint remote)
        {
            udpClient.Send(data, data.Length, remote);
        }
    }
}
