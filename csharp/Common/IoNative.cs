using IronfleetIoFramework;
using System;
using System.Net.Sockets;
using System.Numerics;
using System.Diagnostics;
using System.Threading;
using System.Collections.Concurrent;
using System.Collections.Generic;
using FStream = System.IO.FileStream;
using UClient = System.Net.Sockets.UdpClient;
using IEndPoint = System.Net.IPEndPoint;

namespace IoNative {

  public partial class PrintParams
  {
    internal static bool shouldPrintProfilingInfo = false;
    internal static bool shouldPrintProgress = false;

    public static bool ShouldPrintProfilingInfo() { return shouldPrintProfilingInfo; }
    public static bool ShouldPrintProgress() { return shouldPrintProgress; }

    public static void SetParameters(bool i_shouldPrintProfilingInfo, bool i_shouldPrintProgress)
    {
      shouldPrintProfilingInfo = i_shouldPrintProfilingInfo;
      shouldPrintProgress = i_shouldPrintProgress;
    }
  }

  public partial class IPEndPoint
  {
      internal IEndPoint endpoint;
      internal IPEndPoint(IEndPoint endpoint) { this.endpoint = endpoint; }

      public byte[] GetAddress()
      {
          // no exceptions thrown:
          return (byte[])(endpoint.Address.GetAddressBytes().Clone());
      }

      public ushort GetPort()
      {
          // no exceptions thrown:
          return (ushort)endpoint.Port;
      }

      public static void Construct(byte[] ipAddress, ushort port, out bool ok, out IPEndPoint endpoint)
      {
          try
          {
              ipAddress = (byte[])(ipAddress.Clone());
              endpoint = new IPEndPoint(new IEndPoint(new System.Net.IPAddress(ipAddress), port));
              ok = true;
          }
          catch (Exception e)
          {
              System.Console.Error.WriteLine(e);
              endpoint = null;
              ok = false;
          }
      }
  }

  public struct Packet {
      public IEndPoint ep;
      public byte[] buffer;
  }

  public partial class UdpClient
  {
      internal UClient client;
      internal Thread sender;
      internal Thread receiver;
      internal ConcurrentQueue<Packet> send_queue;
      internal ConcurrentQueue<Packet> receive_queue;

      internal UdpClient(UClient client) { 
        this.client = client;
        this.send_queue = new ConcurrentQueue<Packet>();
        this.receive_queue = new ConcurrentQueue<Packet>();
        this.sender = new Thread(SendLoop);
        this.sender.Start();
        this.receiver = new Thread(ReceiveLoop);
        this.receiver.Start();
      }

      private static bool ShouldIgnoreException(Exception e)
      {
        if (e is SocketException se) {
            if (se.ErrorCode == 10054 /* WSAECONNRESET */) {
              return true;
            }
        }
        return false;
      }

      public static void Construct(IPEndPoint localEP, out bool ok, out UdpClient udp)
      {
          try
          {
              udp = new UdpClient(new UClient(localEP.endpoint));
              udp.client.Client.ReceiveBufferSize = 8192 * 100;
              ok = true;
          }
          catch (Exception e)
          {
              System.Console.Error.WriteLine(e);
              udp = null;
              ok = false;
          }
      }

      public void Close(out bool ok)
      {
          try
          {
              client.Close();
              ok = true;
          }
          catch (Exception e)
          {
              if (ShouldIgnoreException(e)) {
                  ok = true;
              }
              else {
                  System.Console.Error.WriteLine(e);
                  ok = false;
              }
          }
      }

      public void Receive(int timeLimit, out bool ok, out bool timedOut, out IPEndPoint remote, out byte[] buffer)
      {
          buffer = null;
          remote = null;
          try
          {
              Packet packet;
              bool dequeued = this.receive_queue.TryDequeue(out packet);
              if (!dequeued) {
                  if (timeLimit == 0) {
                      ok = true;
                      timedOut = true;
                      return;
                  } else {
                      System.Console.Out.WriteLine("Going to sleep unexpectedly!");
                      Thread.Sleep(timeLimit);  // REVIEW: This is very conservative, but shouldn't matter, since we don't use this path
                      Receive(0, out ok, out timedOut, out remote, out buffer);
                  }
              } else {
  //                System.Console.Out.WriteLine("Dequeued a packet from: " + packet.ep.Address + " port " + packet.ep.Port);
                  timedOut = false;
                  remote = new IPEndPoint(packet.ep);
                  buffer = new byte[packet.buffer.Length];
                  Array.Copy(packet.buffer, buffer, packet.buffer.Length);
                  ok = true;
              }     
          }
          catch (Exception e)
          {
              if (ShouldIgnoreException(e)) {
                  ok = true;
                  timedOut = true;
              }
              else {
                  System.Console.Error.WriteLine(e);
                  timedOut = false;
                  ok = false;
              }
          }
      }

      public void ReceiveLoop() {
          while (true) {
              try {
                  Packet packet = new Packet();
                  packet.buffer = client.Receive(ref packet.ep);
                  this.receive_queue.Enqueue(packet);
                  //System.Console.Out.WriteLine("Enqueued a packet from: " + packet.ep.Address);
              } catch (Exception e) {
                  if (!ShouldIgnoreException(e)) {
                      System.Console.Error.WriteLine(e);
                  }
              }
          }
      }

      public void SendLoop() {
          while (true) {
              try {
                  Packet packet;
                  bool dequeued = this.send_queue.TryDequeue(out packet);
                  if (dequeued) {                
                        int nSent = client.Send(packet.buffer, packet.buffer.Length, packet.ep);
                        if (nSent != packet.buffer.Length) {
                            //throw new Exception("only sent " + nSent + " of " + packet.buffer.Length + " bytes");
                            System.Console.Error.Write("only sent " + nSent + " of " + packet.buffer.Length + " bytes");
                        }                
                  }
              } catch (Exception e) {
                  if (!ShouldIgnoreException(e)) {
                      System.Console.Error.WriteLine(e);
                  }
              }
          }
      }

      public bool Send(IPEndPoint remote, byte[] buffer)
      {
          Packet p = new Packet();
          p.ep = remote.endpoint;
          p.buffer = new byte[buffer.Length];
          Array.Copy(buffer, p.buffer, buffer.Length);
          this.send_queue.Enqueue(p);
          return true; // ok
      }

  }
  
  public class NetClient<BufferType>
  {
    internal IoScheduler<BufferType> scheduler;

    byte[] myPublicKeyHash;

    internal NetClient(IoScheduler<BufferType> i_scheduler, byte[] publicKey)
    {
      scheduler = i_scheduler;
      myPublicKeyHash = scheduler.HashPublicKey(publicKey);
    }

    public static int MaxPublicKeySize { get { return 0xFFFFF; } }

    public byte[] MyPublicKey() { return myPublicKeyHash; }

    public static NetClient<BufferType> Create(PrivateIdentity myIdentity, string localHostNameOrAddress, int localPort,
                                              List<PublicIdentity> knownIdentities, BufferManager<BufferType> bufferManager,
                                              bool verbose, bool useSsl, int maxSendRetries = 3)
    {
      try
      {
        var scheduler = IoScheduler<BufferType>.CreateServer(myIdentity, localHostNameOrAddress, localPort, knownIdentities,
                                                             bufferManager, verbose, useSsl, maxSendRetries);
        var myPublicKey = IronfleetCrypto.GetCertificatePublicKey(scheduler.MyCert);
        if (myPublicKey.Length > MaxPublicKeySize) {
          System.Console.Error.WriteLine("ERROR:  The provided public key for my identity is too big ({0} > {1} bytes)",
                                         myPublicKey.Length, MaxPublicKeySize);
          return null;
        }
        return new NetClient<BufferType>(scheduler, myPublicKey);
      }
      catch (Exception e)
      {
        System.Console.Error.WriteLine(e);
        return null;
      }
    }
  
    public void Receive(int timeLimit, out bool ok, out bool timedOut, out byte[] remote, out Option<BufferType> buffer)
    {
      scheduler.ReceivePacket(timeLimit, out ok, out timedOut, out remote, out buffer);
      if (ok && !timedOut && remote != null && remote.Length > MaxPublicKeySize) {
        ok = false;
      }
    }
  
    public bool Send(Span<byte> remote, Span<byte> buffer)
    {
      return scheduler.SendPacket(remote, buffer);
    }

    public byte[] HashPublicKey(byte[] key)
    {
      return scheduler.HashPublicKey(key);
    }
  }
  
  public class Time
  {
    static Stopwatch watch;
  
    public static void Initialize()
    {
      watch = new Stopwatch();
      watch.Start();
    }
  
    public static ulong GetTime()
    {
      return (ulong) (DateTime.Now.Ticks / 10000);
    }
      
    public static ulong GetDebugTimeTicks()
    {
      return (ulong) watch.ElapsedTicks;
    }
      
    public static void RecordTiming(char[] name, ulong time)
    {
      var str = new string(name);
      IronfleetCommon.Profiler.Record(str, (long)time);
    }
  }
}

