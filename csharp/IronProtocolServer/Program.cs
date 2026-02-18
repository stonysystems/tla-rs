using IronfleetCommon;
using IronfleetIoFramework;
using System;
using System.Linq;
using System.Numerics;
using System.Runtime;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading;
using UClient = System.Net.Sockets.UdpClient;
using IEndPoint = System.Net.IPEndPoint;
using IoNative;

namespace IronProtocolServer
{
    class Program
    {
        static void usage()
        {
        Console.Write(@"
    Usage:  dotnet IronProtocolServer.dll <service> <private> protocol=<name> [key=value]...

    <service>  - file path of the service description
    <private>  - file path of the private key
    protocol   - protocol name: twophase, leaderelection, primarybackup,
                 chainreplication, paxos, verticalpaxos, raft, pbft, epaxos

    Allowed keys:
    addr      - local host name or address to listen to (default:
                whatever's specified in the private key file)
    port      - port to listen to (default: whatever's specified
                in the private key file)
    profile   - print profiling info (false or true, default: false)
    verbose   - use verbose output (false or true, default: false)
    ");
        }

        static IoNative.UdpClient uc;

        [UnmanagedFunctionPointer(CallingConvention.Cdecl)]
        public unsafe delegate void GetMyEndPointDelegate(void** endPoint);

        public unsafe static void GetMyEndPointStatic(void** endPoint)
        {
            var localEP = (System.Net.IPEndPoint)uc.client.Client.LocalEndPoint;

            byte[] ipBytes = localEP.Address.GetAddressBytes();
            ushort port = (ushort)localEP.Port;

            byte[] fullBytes = new byte[ipBytes.Length + 2];
            Array.Copy(ipBytes, fullBytes, ipBytes.Length);
            fullBytes[ipBytes.Length] = (byte)(port >> 8);
            fullBytes[ipBytes.Length + 1] = (byte)(port & 0xFF);

            byte* remoteBuf;
            allocate_buffer((ulong)fullBytes.Length, endPoint, &remoteBuf);
            fullBytes.CopyTo(new Span<byte>(remoteBuf, fullBytes.Length));
        }

        [UnmanagedFunctionPointer(CallingConvention.Cdecl)]
        public unsafe delegate UInt64 GetTimeDelegate();

        public unsafe static UInt64 GetTimeStatic()
        {
            return IoNative.Time.GetTime();
        }

        [UnmanagedFunctionPointer(CallingConvention.Cdecl)]
        public unsafe delegate void ReceiveDelegate(int timeLimit, bool *ok, bool *timedOut, void **remote, void **buffer);

        public unsafe static void ReceiveStatic(int timeLimit, bool *ok, bool *timedOut, void **remote, void **buffer)
        {
            uc.Receive(timeLimit, out bool _ok, out bool _timedOut, out IPEndPoint remoteEp, out byte[] buf);

            *ok = _ok;
            *timedOut = _timedOut;

            if (_ok && !_timedOut)
            {
                byte[] remoteBytes = remoteEp.GetAddress();
                ushort port = remoteEp.GetPort();

                byte[] fullRemote = new byte[remoteBytes.Length + 2];
                Array.Copy(remoteBytes, fullRemote, remoteBytes.Length);
                fullRemote[remoteBytes.Length] = (byte)(port >> 8);
                fullRemote[remoteBytes.Length + 1] = (byte)(port & 0xFF);

                byte* remoteBuf;
                allocate_buffer((ulong)fullRemote.Length, remote, &remoteBuf);
                fullRemote.CopyTo(new Span<byte>(remoteBuf, fullRemote.Length));

                byte* bufferBuf;
                allocate_buffer((ulong)buf.Length, buffer, &bufferBuf);
                buf.CopyTo(new Span<byte>(bufferBuf, buf.Length));
            }
            else
            {
                *remote = null;
                *buffer = null;
            }
        }

        [UnmanagedFunctionPointer(CallingConvention.Cdecl)]
        public unsafe delegate bool SendDelegate(UInt64 remoteLength, byte *remote, UInt64 bufferLength, byte *buffer);

        public unsafe static bool SendStatic(UInt64 remoteLength, byte *remote, UInt64 bufferLength, byte *buffer)
        {
            if (remoteLength < 6UL)
            {
                Console.Error.WriteLine("Remote endpoint too short");
                return false;
            }

            if (remoteLength > int.MaxValue)
            {
                Console.Error.WriteLine("Remote address too long");
                return false;
            }

            int rlen = (int)remoteLength;

            byte[] remoteBytes = new byte[rlen - 2];
            for (int i = 0; i < rlen - 2; i++)
            {
                remoteBytes[i] = remote[i];
            }

            ushort port = (ushort)((remote[remoteLength - 2] << 8) | remote[remoteLength - 1]);

            IPEndPoint.Construct(remoteBytes, port, out bool ok, out IPEndPoint ep);
            if (!ok)
            {
                Console.Error.WriteLine("Failed to construct IPEndPoint");
                return false;
            }

            byte[] sendBuf = new byte[bufferLength];
            if (bufferLength > int.MaxValue)
            {
                Console.Error.WriteLine("Buffer too large");
                return false;
            }

            int len = (int)bufferLength;
            for (int i = 0; i < len; i++)
            {
                sendBuf[i] = buffer[i];
            }

            return uc.Send(ep, sendBuf);
        }


        [DllImport("../liblib.so")]
        public static extern int protocol_main_wrapper(
            byte[] protocolId,
            uint protocolIdLen,
            int numArgs,
            int[] argLengths,
            int totalArgLength,
            byte[] flatArgs,
            GetMyEndPointDelegate getMyEndPointDelegate,
            GetTimeDelegate getTimeDelegate,
            ReceiveDelegate receiveDelegate,
            SendDelegate sendDelegate
        );

        [DllImport("../liblib.so")]
        public unsafe static extern void allocate_buffer(
            UInt64 length,
            void** boxVecPtr,
            byte** bufferPtr
        );

        [DllImport("../liblib.so")]
        public unsafe static extern void free_buffer(
            void* boxVecPtr
        );

        static void FlattenArgs(byte[][] args, out byte[] flatArgs, out int[] argLengths)
        {
            int totalLength = 0;
            foreach (var arg in args) {
                totalLength += arg.Length;
            }
            flatArgs = new byte[totalLength];
            argLengths = new int[args.Length];
            int offset = 0;
            for (int i = 0; i < args.Length; i++) {
                argLengths[i] = args[i].Length;
                Array.Copy(args[i], 0, flatArgs, offset, args[i].Length);
                offset += args[i].Length;
            }
        }

        static void Main(string[] args)
        {
            Params ps = new Params();

            foreach (var arg in args)
            {
                if (!ps.ProcessCommandLineArgument(arg)) {
                usage();
                return;
                }
            }

            if (!ps.Validate()) {
                usage();
                return;
            }

            ServiceIdentity serviceIdentity = ServiceIdentity.ReadFromFile(ps.ServiceFileName);
            if (serviceIdentity == null) {
                return;
            }

            PrivateIdentity privateIdentity = PrivateIdentity.ReadFromFile(ps.PrivateKeyFileName);
            if (privateIdentity == null) {
                return;
            }

            ps.SetHostAndPortFromIdentity(privateIdentity.HostNameOrAddress, privateIdentity.Port);

            IoNative.PrintParams.SetParameters(ps.Profile, i_shouldPrintProgress: false);

            bool ok;
            IPEndPoint ep;
            System.Net.IPAddress ip;
            if (!System.Net.IPAddress.TryParse(ps.LocalHostNameOrAddress, out ip))
            {
                var addresses = System.Net.Dns.GetHostAddresses(ps.LocalHostNameOrAddress);
                if (addresses.Length == 0)
                {
                    Console.Error.WriteLine($"ERROR: Cannot resolve host {ps.LocalHostNameOrAddress}");
                    return;
                }
                ip = addresses[0];
            }
            byte[] ipBytes = ip.GetAddressBytes();

            IPEndPoint.Construct(ipBytes, (ushort)ps.LocalPort, out ok, out ep);

            if (!ok) {
                Console.Error.WriteLine("Failed to construct local IPEndPoint");
                return;
            }

            UdpClient.Construct(ep, out ok, out uc);
            if (!ok) {
                Console.Error.WriteLine("Failed to initialize UDP client");
                return;
            }

            byte[][] serverEndpoints = serviceIdentity.Servers.Select(server =>
            {
                byte[] srvIpBytes = System.Net.IPAddress.Parse(server.HostNameOrAddress).GetAddressBytes();
                ushort port = (ushort)server.Port;
                byte[] epBytes = new byte[srvIpBytes.Length + 2];
                Array.Copy(srvIpBytes, 0, epBytes, 0, srvIpBytes.Length);
                epBytes[srvIpBytes.Length] = (byte)(port >> 8);
                epBytes[srvIpBytes.Length + 1] = (byte)(port & 0xFF);
                return epBytes;
            }).ToArray();

            var ironArgs = serverEndpoints;

            Profiler.Initialize();
            IoNative.Time.Initialize();
            Console.WriteLine($"IronFleet Protocol Server started (protocol: {ps.Protocol}).");
            Console.WriteLine("[[READY]]");

            byte[] flatArgs;
            int[] argLengths;
            FlattenArgs(ironArgs, out flatArgs, out argLengths);

            byte[] protocolBytes = Encoding.UTF8.GetBytes(ps.Protocol);

            unsafe {
                int result = protocol_main_wrapper(
                    protocolBytes,
                    (uint)protocolBytes.Length,
                    argLengths.Length,
                    argLengths,
                    flatArgs.Length,
                    flatArgs,
                    GetMyEndPointStatic,
                    GetTimeStatic,
                    ReceiveStatic,
                    SendStatic
                );
                if (result != 0) {
                    Console.Error.WriteLine($"Protocol exited with code {result}");
                }
            }

            Console.WriteLine("[[EXIT]]");
        }
    }

    public unsafe class RustBuffer
    {
        private void* boxVecPtr;
        private byte* bufferPtr;
        private UInt64 length;

        public RustBuffer(void* i_boxVecPtr, byte* i_bufferPtr, UInt64 i_length)
        {
        boxVecPtr = i_boxVecPtr;
        bufferPtr = i_bufferPtr;
        length = i_length;
        }

        public void* BoxVecPtr { get { return boxVecPtr; } }
        public byte* BufferPtr { get { return bufferPtr; } }
        public UInt64 Length { get { return length; } }
    }

    public class RustBufferManager : BufferManager<RustBuffer>
    {
        public unsafe RustBuffer AllocateNewBuffer(UInt64 length)
        {
        void *boxVecPtr;
        byte* bufferPtr;
        if (length > Int32.MaxValue) {
            throw new Exception("Currently no support for buffers this big");
        }
        Program.allocate_buffer(length, &boxVecPtr, &bufferPtr);
        return new RustBuffer(boxVecPtr, bufferPtr, length);
        }

        public unsafe Span<byte> BufferToSpan(RustBuffer buffer)
        {
        return new Span<byte>(buffer.BufferPtr, (int)buffer.Length);
        }

        public unsafe void FreeBuffer(RustBuffer buffer)
        {
        Program.free_buffer(buffer.BoxVecPtr);
        }
    }
}
