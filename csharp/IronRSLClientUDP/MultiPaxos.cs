namespace IronRSLClientUDP
{
    using System;
    using System.IO;
    using System.Net;
    using System.Threading;
    using System.Diagnostics;
    using System.Linq;

    public class RequestMessage : MessageBase
    {
        public byte[] Value { get; set; }
        public ulong seqNum;
        public ulong myaddr;

        public RequestMessage(ulong seqNum, ulong myaddr)
            : base(0)
        {
            this.seqNum = seqNum;
            this.myaddr = myaddr;
        }

        public override byte[] ToBigEndianByteArray()
        {
            return this.Encode();
        }

        public ulong GetSeqNum()
        {
            return seqNum;
        }

        protected void EncodeTag(MemoryStream memStream, byte value)
        {
            memStream.WriteByte(value);
        }

        static (bool, byte) DecodeTag(byte[] bytes, ref int offset)
        {
            if (bytes.Length < offset + 1) {
                return (false, 0);
            }
            byte result = bytes[offset];
            offset += 1;
            return (true, result);
        }

        protected void EncodeUlong(MemoryStream memStream, ulong value)
        {
            if (null == memStream)
            {
                throw new ArgumentNullException("memStream");
            }

            var bytes = BitConverter.GetBytes(value);
            if (!BitConverter.IsLittleEndian)
            {
                // NB Ironfleet 2015 used big-endian marshalling
                // Verus 2023 uses little-endian marshalling
                Array.Reverse(bytes);
            }
            memStream.Write(bytes, 0, bytes.Length);
        }

        public static (bool, UInt64) ExtractLE64(byte[] byteArray, ref int offset)
        {
            if (byteArray.Length < offset + 8) {
                return (false, 0);
            }
            byte[] extractedBytes = byteArray.Skip(offset).Take(8).ToArray();
            if (!BitConverter.IsLittleEndian) {
                Array.Reverse(extractedBytes);
            }
            offset += 8;
            return (true, BitConverter.ToUInt64(extractedBytes, 0));
        }


        private byte[] Encode()
        {

            using (var memStream = new MemoryStream())
            {
                // this.EncodeHeader(memStream); // case for CMessage_Request
                // this.EncodeUlong(memStream, (ulong)seqNum); // field one in CMessage_Request
                // this.EncodeUlong(memStream, (ulong)0); // case for CAppMessageIncrement    
                EncodeTag(memStream, 1);           
                EncodeUlong(memStream, (ulong)seqNum);
                EncodeTag(memStream, 0);
                return memStream.ToArray();
            }
        }
    }

    public class Client : ClientBase
    {
        public static bool DEBUG = false;

        //private static long num_reqs = 0;

        // public int []num_req_cnt_a;
        // public double []latency_cnt_ms_a;



        public static void Trace(string str)
        {
            if (DEBUG)
            {
                Console.Out.WriteLine(str);
            }    
        }
  

        public string ByteArrayToString(byte[] ba)
        {
            string hex = BitConverter.ToString(ba);
            return hex.Replace("-", "");
        }

        protected void EncodeTag(MemoryStream memStream, byte value)
        {
            memStream.WriteByte(value);
        }

        static (bool, byte) DecodeTag(byte[] bytes, ref int offset)
        {
            if (bytes.Length < offset + 1) {
                return (false, 0);
            }
            byte result = bytes[offset];
            offset += 1;
            return (true, result);
        }

        protected void EncodeUlong(MemoryStream memStream, ulong value)
        {
            if (null == memStream)
            {
                throw new ArgumentNullException("memStream");
            }

            var bytes = BitConverter.GetBytes(value);
            if (!BitConverter.IsLittleEndian)
            {
                // NB Ironfleet 2015 used big-endian marshalling
                // Verus 2023 uses little-endian marshalling
                Array.Reverse(bytes);
            }
            memStream.Write(bytes, 0, bytes.Length);
        }

        public static (bool, UInt64) ExtractLE64(byte[] byteArray, ref int offset)
        {
            if (byteArray.Length < offset + 8) {
                return (false, 0);
            }
            byte[] extractedBytes = byteArray.Skip(offset).Take(8).ToArray();
            if (!BitConverter.IsLittleEndian) {
                Array.Reverse(extractedBytes);
            }
            offset += 8;
            return (true, BitConverter.ToUInt64(extractedBytes, 0));
        }

        protected void ReceiveLoop() {
            byte[] bytes;
            while (true)
            {
                bytes = Receive();
                var end_time = (ulong)HiResTimer.Ticks;
                Trace("Got the following reply:" + ByteArrayToString(bytes));
                if (bytes.Length == 40)
                {
                    var start_time = ExtractBE64(bytes, 32);
                    var request_time = end_time - start_time;

                    Trace("Request took " + request_time + " ticks");
                    Console.WriteLine(request_time);
                }
                else
                {
                    Trace("Got an unexpected packet length: " + bytes.Length);
                }
            }
        }

        protected override void Main(int id, int port_num, ulong initial_seq_no, int []num_req_cnt_a_, double []latency_cnt_ms_a_)
        {
            this.udpClient = new System.Net.Sockets.UdpClient(port_num+(int)id);
            this.udpClient.Client.ReceiveTimeout = 1000;
            // this.num_req_cnt_a = num_req_cnt_a_;
            // this.latency_cnt_ms_a = latency_cnt_ms_a_;
            ulong myaddr = MyAddress64();

            int serverIdx = 0;
            
            for (ulong seq_no = initial_seq_no; true; ++seq_no)
            {
                // Make the sequence number a time stamp
                //var newSeqNum = (ulong) HiResTimer.UtcNow.Ticks;
                //if (newSeqNum == seqNum) {
                //    seqNum = newSeqNum + 1;
                //}
                //else
                //{
                //    seqNum = newSeqNum;
                //}

                var msg = new RequestMessage(seq_no, myaddr);

                Trace("Client " + id.ToString() + ": Sending a request with a sequence number " + msg.GetSeqNum() + " to " + ClientBase.endpoints[serverIdx].ToString());

                var start_time = HiResTimer.Ticks;
                this.Send(msg, ClientBase.endpoints[serverIdx]);
                //foreach (var remote in ClientBase.endpoints)
                //{
                //    this.Send(msg, remote);
                //}

                // Wait for the reply
                var received_reply = false;
                while (!received_reply)
                {
                    byte[] bytes;
                    try
                    {
                        bytes = Receive();
                    }
                    catch (System.Net.Sockets.SocketException e)
                    {
                        serverIdx = (serverIdx + 1) % ClientBase.endpoints.Count();
                        // Console.WriteLine("#timeout; rotating to server {0}", serverIdx);
                        // Console.WriteLine(e.ToString());
                        break;
                    }
                    var end_time = HiResTimer.Ticks;
                    Trace("Got the following reply:" + ByteArrayToString(bytes));
                    double latency = 0;

                    if (bytes.Length == 18)
                    {
                        int offset = 0;
                        (bool ok1, byte messageType) = DecodeTag(bytes, ref offset);
                        if (!ok1 || messageType != 7) {
                            throw new Exception("Got RSL message that wasn't a reply");
                        }

                        (bool ok2, UInt64 replySeqNum) = ExtractLE64(bytes, ref offset);

                        // var reply_seq_no = ExtractBE64(bytes, offset: 8);
                        if (replySeqNum == seq_no)
                        {
                            received_reply = true;
                            // Report time in milliseconds, since that's what the Python script appears to expect
                            latency = HiResTimer.TicksToMilliseconds(end_time - start_time);
                            // Console.Out.WriteLine(string.Format("#req{0} {1} {2}", seq_no, latency, id));
                            //long n = Interlocked.Increment(ref num_reqs);
                            //if (1 == n || n % 1000 == 0)
                            //{
                            //    Console.WriteLine("{0} requests completed.", n);
                            //}
                            num_req_cnt_a_[id] += 1;
                            latency_cnt_ms_a_[id] += latency;
                        } else {
                            // Console.Out.WriteLine("reply seq no: {0}", reply_seq_no);
                        }
                    }
                    else
                    {
                        Console.Error.WriteLine("Got an unexpected packet length: " + bytes.Length);
                    }
                }
            }
        }
    }
}
