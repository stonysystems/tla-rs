# -*- python -*-
import atexit
import os, os.path
import re
import shutil
import subprocess
import sys
import SCons.Util
import threading

Import("*")

# Retrieve tool-specific command overrides passed in by the user
AddOption('--verus-path',
  dest='verus_path',
  type='string',
  nargs=1,
  default=None,
  action='store',
  help='Specify the path to your local copy of the Verus repo')

AddOption('--no-verify',
  dest='no_verify',
  default=False,
  action='store_true',
  help="Don't verify, just build executables")

AddOption('--skip-verus',
  dest='skip_verus',
  default=False,
  action='store_true',
  help="Skip Verus verification, only build C# projects")

AddOption('--skip-dotnet',
  dest='skip_dotnet',
  default=False,
  action='store_true',
  help="Skip .NET/C# builds, only run Verus verification")

AddOption('--debug-build',
  dest='debug_build',
  default=False,
  action='store_true',
  help="Build executables in debug mode")

verus_path = GetOption('verus_path')
if verus_path is None and not GetOption('skip_verus'):
  sys.stderr.write("ERROR:  Missing --verus-path= on command line (use --skip-verus to skip Verus verification)\n")
  exit(-1)

#verus_variant = "debug" if GetOption('debug_build') else "release"
verus_variant = "release"
# verus_script = os.path.join(verus_path, f"source/target-verus/{verus_variant}/verus")
verus_script = verus_path
if verus_script is not None:
  if sys.platform == 'win32':
      verus_script = verus_script + ".exe"
  if not os.path.exists(verus_script):
    sys.stderr.write("ERROR:  Could not find %s\n" % (verus_script))
    exit(-1)

env = Environment(ENV=os.environ)

####################################################################
#
#   .NET binaries
#
####################################################################

def generate_dotnet_actions(source, target, env, for_signature):
  target_dir = os.path.dirname(str(target[0]))
  build_config = "Debug" if GetOption('debug_build') else "Release"
  return [
    ["dotnet", "build", "--configuration", build_config, "--output", target_dir, str(source[0])]
  ]

def get_dotnet_dependencies(target, source, env):
  csproj_file = str(source[0])
  source_dir = os.path.dirname(csproj_file)
  extra_dependencies = [os.path.join(source_dir, f) for f in os.listdir(source_dir) if re.search(r'\.cs$', f)]
  with open(csproj_file, 'r') as fh:
    for line in fh.readlines():
      m = re.search(r'<Compile\s+Include=\"([^\"]*)\"\s*/>', line)
      if m:
        raw_file_name = re.sub(r'\\', '/', m.group(1))
        file_name = os.path.normpath(os.path.join(source_dir, raw_file_name))
        extra_dependencies.append(file_name)
  return target, source + extra_dependencies

# Add env.DotnetBuild(), to generate dotnet build actions
def add_dotnet_builder(env):
  client_builder = Builder(generator = generate_dotnet_actions,
                           chdir=0,
                           emitter=get_dotnet_dependencies)
  env.Append(BUILDERS = {'DotnetBuild' : client_builder})


####################################################################
#
#   Verus binaries
#
####################################################################

def generate_verus_actions(source, target, env, for_signature):
  source_dir = os.path.dirname(str(source[0]))
  # [jonh] NB -C opt-level=3 is the default; I don't think it does
  # anything here.
  # https://users.rust-lang.org/t/do-rust-compilers-have-optimization-flags-like-c-compilers-have/48833/7
  opt_flag = ["-g"] if GetOption('debug_build') else ["-C", "opt-level=3"]
  cmd_line = [verus_script, "--crate-type=dylib", "--expand-errors"] + opt_flag + ["--compile", str(source[0])]
  if GetOption("no_verify"):
      cmd_line.append("--no-verify")
  return [ cmd_line ]

def get_verus_dependencies(target, source, env):
  source_dir = os.path.dirname(str(source[0]))

  extra_dependencies = []
  for root, _, files in os.walk(source_dir):
    for f in files:
      if f.endswith('.rs'):
        extra_dependencies.append(os.path.join(root, f))

  return target, source + extra_dependencies

# Add env.VerusBuild(), to generate Verus build actions
def add_verus_builder(env):
  client_builder = Builder(generator = generate_verus_actions,
                           chdir=0,
                           emitter=get_verus_dependencies)
  env.Append(BUILDERS = {'VerusBuild' : client_builder})
  
####################################################################
#
#   Put it all together
#
####################################################################

add_dotnet_builder(env)
add_verus_builder(env)

####################################################################
#
#   Create dependencies
#
####################################################################

if not GetOption('skip_dotnet'):
  # env.DotnetBuild('bin/IronLockServer.dll', 'csharp/IronLockServer/IronLockServer.csproj')
  env.DotnetBuild('bin/IronRSLClient.dll', 'csharp/IronRSLClient/IronRSLClient.csproj')
  env.DotnetBuild('bin/IronRSLServer.dll', 'csharp/IronRSLServer/IronRSLServer.csproj')
  env.DotnetBuild('bin/IronRSLClientUDP.dll', 'csharp/IronRSLClientUDP/IronRSLClientUDP.csproj')
  env.DotnetBuild('bin/IronRSLServerUDP.dll', 'csharp/IronRSLServerUDP/IronRSLServerUDP.csproj')
  env.DotnetBuild('bin/CreateIronServiceCerts.dll', 'csharp/CreateIronServiceCerts/CreateIronServiceCerts.csproj')
  env.DotnetBuild('bin/TestIoFramework.dll', 'csharp/TestIoFramework/TestIoFramework.csproj')
  env.DotnetBuild('bin/IronProtocolServer.dll', 'csharp/IronProtocolServer/IronProtocolServer.csproj')
  env.DotnetBuild('bin/IronRaftClient.dll', 'csharp/IronRaftClient/IronRaftClient.csproj')

if not GetOption('skip_verus'):
  env.VerusBuild('liblib.so', 'src/lib.rs')
