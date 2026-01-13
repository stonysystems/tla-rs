using IronfleetCommon;
using IronfleetIoFramework;
using System;
using System.Linq;
using System.Numerics;
using System.Threading;
using System.IO;
using System.Net;
using System.Collections.Generic;

namespace IronRSLClient
{
  class Program
  {
    static void usage()
    {
      Console.Write(@"
Usage:  dotnet IronRSLCounterClient.dll <service> [key=value]...

  <service> - file path of the service description

Allowed keys:
  nthreads  - number of client threads to run (default 1)
  duration  - duration of experiment in seconds (default 60)
  print     - print replies (false or true, default false)
  verbose   - print verbose output (false or true, default false)
");
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
      
      if (!ps.Validate())
      {
        usage();
        return;
      }

      var serviceIdentity = ServiceIdentity.ReadFromFile(ps.ServiceFileName);
      if (serviceIdentity == null) {
        return;
      }

      HiResTimer.Initialize();
      if (ps.Verbose) {
        Console.WriteLine("Client process starting {0} threads running for {1} s...", ps.NumThreads, ps.ExperimentDuration);
      }
            
      Console.WriteLine("[[READY]]");

      int[] num_req_cnt_a = new int[ps.NumThreads];
      double[] latency_cnt_ms_a = new double[ps.NumThreads];
      
      Array.Clear(num_req_cnt_a, 0, ps.NumThreads);
      Array.Clear(latency_cnt_ms_a, 0, ps.NumThreads);
            
      // Start the experiment
      var threads = IronRSLClient.Client.StartThreads(ps, serviceIdentity, num_req_cnt_a, latency_cnt_ms_a).ToArray();

      if (ps.ExperimentDuration == 0)
      {
        threads[0].Join();
      }
      else
      {
        Thread.Sleep((int)ps.ExperimentDuration * 1000);
        Console.Out.WriteLine("[[DONE]]");
        Console.Out.Flush();

        int total_num_req_cnt = 0;
        double total_latency_cnt_ms = 0;

        for (int i = 0; i < ps.NumThreads; ++i)
        {
        	int num_req_cnt = num_req_cnt_a[i];
        	double latency_cnt_ms = latency_cnt_ms_a[i];
			
          total_num_req_cnt += num_req_cnt;
          total_latency_cnt_ms += latency_cnt_ms;
        }
        
        Console.WriteLine("throughput {0} | avg latency ms {1}", total_num_req_cnt / (int) (ps.ExperimentDuration-8), total_latency_cnt_ms / total_num_req_cnt);
        // Console.WriteLine("throughput {0} | avg latency ms {1}", total_num_req_cnt / (int) (total_latency_cnt_ms/1000), total_latency_cnt_ms / total_num_req_cnt);

        Environment.Exit(0);
      }
    }
  }
}
