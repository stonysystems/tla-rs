using IronfleetIoFramework;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;
using System.Threading.Tasks;

namespace IronRSLClient
{
  public class RSLClient
  {
    ServiceIdentity serviceIdentity;
    byte[][] serverPublicKeys;
    bool verbose;
    UInt64 nextSeqNum;
    int primaryServerIndex;
    IoScheduler<byte[]> scheduler;
    private ArrayBufferManager bufferManager;

    public RSLClient(ServiceIdentity i_serviceIdentity, string serviceName, bool i_verbose)
    {
      IoTimer.Initialize();
      serviceIdentity = i_serviceIdentity;
      if (serviceIdentity.ServiceType != "IronRSL" + serviceName) {
        Console.Error.WriteLine("Provided service identity has type {0}, not IronRSL{1}.",
                                serviceIdentity.ServiceType, serviceName);
        throw new Exception("Wrong service type");
      }
      verbose = i_verbose;
      nextSeqNum = 0;
      primaryServerIndex = 0;
      bufferManager = new ArrayBufferManager();
      scheduler = IoScheduler<byte[]>.CreateClient(serviceIdentity.Servers, bufferManager, verbose, serviceIdentity.UseSsl);
      serverPublicKeys = serviceIdentity.Servers.Select(server => scheduler.HashPublicKey(server.PublicKey)).ToArray();
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

    public byte[] SubmitRequest (byte[] request, int timeBeforeServerSwitchMs = 1000)
    {
      UInt64 seqNum = nextSeqNum++;
      byte[] requestMessage;
      using (var memStream = new MemoryStream())
      {
        // IoEncoder.WriteUInt64(memStream, 1);              // CMessage_Request type = 0
        EncodeTag(memStream, 1);
        // IoEncoder.WriteUInt64(memStream, seqNum);         // Field 1: Sequence number
        EncodeUlong(memStream, (ulong)seqNum);
        EncodeTag(memStream, 0);              // CAppMessageIncrement type = 0
        // IoEncoder.WriteUInt64(memStream, MyAddr);         // Optional: encode address if needed
        requestMessage = memStream.ToArray();
      }

      scheduler.SendPacket(serverPublicKeys[primaryServerIndex], requestMessage);
      if (verbose) {
        Console.WriteLine("Sending a request with sequence number {0} to {1}",
                          seqNum, serviceIdentity.Servers[primaryServerIndex]);
      }

      while (true)
      {
        bool ok, timedOut;
        byte[] remote;
        Option<byte[]> replyBytes;
        scheduler.ReceivePacket(timeBeforeServerSwitchMs, out ok, out timedOut, out remote, out replyBytes);

        if (!ok) {
          throw new Exception("Unrecoverable networking failure");
        }

        if (timedOut) {
          primaryServerIndex = (primaryServerIndex + 1) % serviceIdentity.Servers.Count();
          if (verbose) {
            Console.WriteLine("#timeout; rotating to server {0}", primaryServerIndex);
          }
          scheduler.SendPacket(serverPublicKeys[primaryServerIndex], requestMessage);
          continue;
        }

        if (replyBytes is Some<byte[]> some) {
          byte[] reply = some.Value;
          if (reply.Length < 18) {
            throw new Exception(String.Format("Got RSL reply with invalid length {0}", reply.Length));
          }

          int offset = 0;

          (bool ok1, byte messageType) = DecodeTag(reply, ref offset);
          if (!ok1 || messageType != 7) {
            throw new Exception("Got RSL message that wasn't a reply");
          }

          (bool ok2, UInt64 replySeqNum) = ExtractLE64(reply, ref offset);
          if (!ok2 || replySeqNum != seqNum) {
            // This is a retransmission of a reply for an old sequence
            // number.  Ignore it.
            continue;
          }
          
          // UInt64 replyLength = IoEncoder.ExtractUInt64(reply, 16);
          // if (replyLength + 24 != (UInt64)reply.Length) {
          //   throw new Exception(String.Format("Got RSL reply with invalid encoded length ({0} instead of {1})",
          //                                     replyLength, reply.Length - 24));
          // }

          return reply.Skip(10).ToArray();
        } else {
          return null;
        }
      }
    }
  }
}
