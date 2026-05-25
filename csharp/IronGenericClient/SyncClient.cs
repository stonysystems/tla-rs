using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Net;
using System.Net.Sockets;
using System.Threading;

namespace IronGenericClient
{
    /// <summary>
    /// Protocol adapter: encodes requests and decodes replies for a specific protocol.
    /// </summary>
    public interface IProtocolAdapter
    {
        byte[] EncodeRequest(ulong clientId, ulong seqNo);

        /// <summary>
        /// Try to decode a reply. Returns true if the packet is a valid reply.
        /// isMatch: true if it matches the given clientId/seqNo (always true for
        /// protocols without matching). isSuccess: true if the reply indicates success.
        /// </summary>
        bool TryDecodeReply(byte[] data, ulong clientId, ulong seqNo,
                            out bool isMatch, out bool isSuccess);
    }

    /// <summary>
    /// Synchronous benchmark client. Sends one request at a time, waits for
    /// a matching reply with timeout, and rotates servers on timeout.
    /// </summary>
    public class SyncClient
    {
        private const int RECEIVE_TIMEOUT_MS = 50;

        private readonly IProtocolAdapter adapter;
        private readonly List<IPEndPoint> endpoints;
        private readonly ulong clientId;
        private UdpClient udp;

        public SyncClient(IProtocolAdapter adapter, List<IPEndPoint> endpoints, int localPort)
        {
            this.adapter = adapter;
            this.endpoints = endpoints;
            this.clientId = (ulong)localPort;
            this.udp = new UdpClient(localPort);
            this.udp.Client.ReceiveTimeout = RECEIVE_TIMEOUT_MS;
        }

        public void Run(int threadId, int[] reqCounts, double[] latencySums,
                        int[] sharedLeaderIdx, int[] running)
        {
            Thread.Sleep(3000); // startup delay

            int serverIdx = Volatile.Read(ref sharedLeaderIdx[0]);
            if (serverIdx < 0 || serverIdx >= endpoints.Count)
                serverIdx = 0;

            for (ulong seqNo = 0; Volatile.Read(ref running[0]) == 1; seqNo++)
            {
                byte[] request = adapter.EncodeRequest(clientId, seqNo);
                var startTime = HiResTimer.Ticks;
                udp.Send(request, request.Length, endpoints[serverIdx]);

                bool receivedReply = false;
                while (!receivedReply && Volatile.Read(ref running[0]) == 1)
                {
                    byte[] bytes;
                    try
                    {
                        IPEndPoint sender = null;
                        bytes = udp.Receive(ref sender);
                    }
                    catch (SocketException)
                    {
                        serverIdx = (serverIdx + 1) % endpoints.Count;
                        udp.Send(request, request.Length, endpoints[serverIdx]);
                        continue;
                    }

                    if (!adapter.TryDecodeReply(bytes, clientId, seqNo,
                                                out bool isMatch, out bool isSuccess))
                        continue;
                    if (!isMatch) continue;
                    if (!isSuccess)
                    {
                        serverIdx = (serverIdx + 1) % endpoints.Count;
                        udp.Send(request, request.Length, endpoints[serverIdx]);
                        continue;
                    }

                    receivedReply = true;
                    Volatile.Write(ref sharedLeaderIdx[0], serverIdx);
                    double latencyMs = HiResTimer.TicksToMilliseconds(
                        HiResTimer.Ticks - startTime);
                    reqCounts[threadId] += 1;
                    latencySums[threadId] += latencyMs;
                }
            }

            udp.Close();
        }
    }

    // ─── Wire format helpers ─────────────────────────────────────────

    static class Wire
    {
        public static void WriteLE64(MemoryStream ms, ulong value)
        {
            byte[] bytes = BitConverter.GetBytes(value);
            if (!BitConverter.IsLittleEndian) Array.Reverse(bytes);
            ms.Write(bytes, 0, bytes.Length);
        }

        public static ulong ReadLE64(byte[] data, ref int offset)
        {
            if (!BitConverter.IsLittleEndian)
            {
                byte[] tmp = new byte[8];
                Array.Copy(data, offset, tmp, 0, 8);
                Array.Reverse(tmp);
                offset += 8;
                return BitConverter.ToUInt64(tmp, 0);
            }
            ulong val = BitConverter.ToUInt64(data, offset);
            offset += 8;
            return val;
        }
    }

    // ─── Protocol Adapters ───────────────────────────────────────────

    /// <summary>
    /// Raft: Send [5][client_id][seq_no][value]=32B, Recv [6][client_id][seq_no][success]=32B
    /// </summary>
    public class RaftAdapter : IProtocolAdapter
    {
        public byte[] EncodeRequest(ulong clientId, ulong seqNo)
        {
            var ms = new MemoryStream(32);
            Wire.WriteLE64(ms, 5);
            Wire.WriteLE64(ms, clientId);
            Wire.WriteLE64(ms, seqNo);
            Wire.WriteLE64(ms, seqNo);
            return ms.ToArray();
        }

        public bool TryDecodeReply(byte[] data, ulong clientId, ulong seqNo,
                                   out bool isMatch, out bool isSuccess)
        {
            isMatch = false; isSuccess = false;
            if (data.Length < 32) return false;
            int off = 0;
            if (Wire.ReadLE64(data, ref off) != 6) return false;
            ulong rCid = Wire.ReadLE64(data, ref off);
            ulong rSeq = Wire.ReadLE64(data, ref off);
            ulong rOk  = Wire.ReadLE64(data, ref off);
            isMatch = (rCid == clientId && rSeq == seqNo);
            isSuccess = (rOk != 0);
            return true;
        }
    }

    /// <summary>PB: Send [3][value]=16B, Recv [4][value]=16B</summary>
    public class PBAdapter : IProtocolAdapter
    {
        public byte[] EncodeRequest(ulong clientId, ulong seqNo)
        {
            var ms = new MemoryStream(16);
            Wire.WriteLE64(ms, 3);
            Wire.WriteLE64(ms, seqNo);
            return ms.ToArray();
        }

        public bool TryDecodeReply(byte[] data, ulong clientId, ulong seqNo,
                                   out bool isMatch, out bool isSuccess)
        {
            isMatch = false; isSuccess = false;
            if (data.Length < 16) return false;
            int off = 0;
            if (Wire.ReadLE64(data, ref off) != 4) return false;
            isMatch = true; isSuccess = true;
            return true;
        }
    }

    /// <summary>PBFT: Send [4][digest]=16B, Recv [5][digest]=16B</summary>
    public class PBFTAdapter : IProtocolAdapter
    {
        public byte[] EncodeRequest(ulong clientId, ulong seqNo)
        {
            var ms = new MemoryStream(16);
            Wire.WriteLE64(ms, 4);
            Wire.WriteLE64(ms, seqNo);
            return ms.ToArray();
        }

        public bool TryDecodeReply(byte[] data, ulong clientId, ulong seqNo,
                                   out bool isMatch, out bool isSuccess)
        {
            isMatch = false; isSuccess = false;
            if (data.Length < 16) return false;
            int off = 0;
            if (Wire.ReadLE64(data, ref off) != 5) return false;
            isMatch = true; isSuccess = true;
            return true;
        }
    }

    /// <summary>EPaxos: Send [6][cmd]=16B, Recv [7][cmd]=16B</summary>
    public class EPaxosAdapter : IProtocolAdapter
    {
        public byte[] EncodeRequest(ulong clientId, ulong seqNo)
        {
            var ms = new MemoryStream(16);
            Wire.WriteLE64(ms, 6);
            Wire.WriteLE64(ms, seqNo);
            return ms.ToArray();
        }

        public bool TryDecodeReply(byte[] data, ulong clientId, ulong seqNo,
                                   out bool isMatch, out bool isSuccess)
        {
            isMatch = false; isSuccess = false;
            if (data.Length < 16) return false;
            int off = 0;
            if (Wire.ReadLE64(data, ref off) != 7) return false;
            isMatch = true; isSuccess = true;
            return true;
        }
    }

    // ─── HiResTimer ──────────────────────────────────────────────────

    public class HiResTimer
    {
        private static Stopwatch _stopWatch;
        public static long Ticks => _stopWatch.ElapsedTicks;
        public static void Initialize() { _stopWatch = Stopwatch.StartNew(); }
        public static double TicksToMilliseconds(long ticks)
            => ticks * 1000.0 / Stopwatch.Frequency;
    }
}
