using IronfleetCommon;
using IronfleetIoFramework;
using System;
using System.Linq;
using System.Numerics;
using System.Runtime;
using System.Runtime.InteropServices;
using System.Threading;

namespace IronLockServer
{
  class Program
  {
    static void usage()
    {
      Console.Write(@"
Usage:  dotnet IronLockServer.dll <service> <private> [key=value]...

  <service> - file path of the service description
  <private> - file path of the private key

Allowed keys:
  addr      - local host name or address to listen to (default:
              whatever's specified in the private key file)
  port      - port to listen to (default: whatever's specified
              in the private key file)
  profile   - print profiling info (false or true, default: false)
  verbose   - use verbose output (false or true, default: false)
");
    }

    // We make `nc` static so that the C-style callbacks we pass to Verus can use it.
    static IoNative.NetClient<RustBuffer> nc;
    
    [UnmanagedFunctionPointer(CallingConvention.Cdecl)]
    public unsafe delegate void GetMyEndPointDelegate(void** endPoint);

    public unsafe static void GetMyEndPointStatic(void** endPoint)
    {
      byte[] endPointArray = nc.MyPublicKey();
      byte* endPointBuf;
      allocate_buffer((ulong)endPointArray.Length, endPoint, &endPointBuf);
      Span<byte> endPointSpan = new Span<byte>(endPointBuf, endPointArray.Length);
      MemoryExtensions.CopyTo(endPointArray, endPointSpan);
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
      Option<RustBuffer> rustBuffer;
      byte[] remoteArray;
      nc.Receive(timeLimit, out *ok, out *timedOut, out remoteArray, out rustBuffer);
      if (*ok && !*timedOut) {
        if (rustBuffer is Some<RustBuffer> some)  {
          byte* remoteBuf;
          allocate_buffer((ulong)remoteArray.Length, remote, &remoteBuf);
          Span<byte> remoteSpan = new Span<byte>(remoteBuf, remoteArray.Length);
          MemoryExtensions.CopyTo(remoteArray, remoteSpan);
          *buffer = some.Value.BoxVecPtr;
        }
        else {
          *remote = null;
          *buffer = null;
          *ok = false;
        }
      }
      else {
        *remote = null;
        *buffer = null;
      }
    }
    
    [UnmanagedFunctionPointer(CallingConvention.Cdecl)]
    public unsafe delegate bool SendDelegate(UInt64 remoteLength, byte *remote, UInt64 bufferLength, byte *buffer);

    public unsafe static bool SendStatic(UInt64 remoteLength, byte *remote, UInt64 bufferLength, byte *buffer)
    {
      Span<byte> remoteSpan = new Span<byte>(remote, (int)remoteLength);
      Span<byte> bufferSpan = new Span<byte>(buffer, (int)bufferLength);
      return nc.Send(remoteSpan, bufferSpan);
    }

    [DllImport("../lib.dll")]
    public static extern void lock_main_wrapper(
      int numArgs,
      int[] argLengths,
      int totalArgLength,
      byte[] flatArgs,
      GetMyEndPointDelegate getMyEndPointDelegate,
      GetTimeDelegate getTimeDelegate,
      ReceiveDelegate receiveDelegate,
      SendDelegate sendDelegate
    );

    [DllImport("../lib.dll")]
    public unsafe static extern void allocate_buffer(
      UInt64 length,
      void** boxVecPtr,
      byte** bufferPtr
    );

    [DllImport("../lib.dll")]
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
      Console.WriteLine("IronLockServer program started");

      Console.WriteLine("Processing command-line arguments");

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
      if (serviceIdentity.ServiceType != "IronLock") {
        Console.Error.WriteLine("ERROR - Service described by {0} is of type {1}, not IronLock", ps.ServiceFileName,
                                serviceIdentity.ServiceType);
        return;
      }

      PrivateIdentity privateIdentity = PrivateIdentity.ReadFromFile(ps.PrivateKeyFileName);
      if (privateIdentity == null) {
        return;
      }

      IoNative.PrintParams.SetParameters(ps.Profile, i_shouldPrintProgress: false);

      RustBufferManager rustBufferManager = new RustBufferManager();
      nc = IoNative.NetClient<RustBuffer>.Create(privateIdentity, ps.LocalHostNameOrAddress, ps.LocalPort,
                                                 serviceIdentity.Servers, rustBufferManager, ps.Verbose, serviceIdentity.UseSsl);
      byte[][] serverPublicKeys = serviceIdentity.Servers.Select(server => nc.HashPublicKey(server.PublicKey)).ToArray();
      var ironArgs = serverPublicKeys;

      Profiler.Initialize();
      IoNative.Time.Initialize();
      Console.WriteLine("IronFleet program started.");
      Console.WriteLine("[[READY]]");
      byte[] flatArgs;
      int[] argLengths;
      FlattenArgs(ironArgs, out flatArgs, out argLengths);
      unsafe {
        lock_main_wrapper(argLengths.Length, argLengths, flatArgs.Length, flatArgs, GetMyEndPointStatic, GetTimeStatic, ReceiveStatic, SendStatic);
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

