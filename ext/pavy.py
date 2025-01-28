#!/usr/bin/env python

import sys
import os
import os.path
import atexit
import tempfile
import shutil
import subprocess as sub
import threading
import signal
import time
import resource
import itertools

import aig

#
# globals ...
#
root = os.path.dirname(os.path.realpath(__file__))
running = list()    # list of running processes

###############################################################################

class SolverCfg(object):
    def __init__(self, name, cmd, cpu=-1, mem=-1):
        self._name = name
        self._cmd = cmd
        self._cpu = cpu
        self._mem = mem
        
    @property
    def name(self): return self._name
    @property 
    def cmd(self): return self._cmd
    @property
    def cpu(self): return self._cpu
    @property
    def mem(self): return self._mem
    
    def append_arg(self, arg): self._cmd.append(arg)

    def set_witness_output(self, cex, cert):
        self.append_arg('--cex={0}'.format(cex))
        self.append_arg('--certificate={0}'.format(cert))

    def verbose(self, level):
        self.append_arg('--verbose={0}'.format(level))

    def set_time_limit(self, arg): self._cpu = arg
    def set_memory_limit(self, arg): self._mem = arg

    def __str__(self):
        return '[' + self.name + '] ' + ' '.join(self.cmd)

    def binary_certificate(self): return True

class RfvConfig(SolverCfg):
    def __init__(self, name, cmd, cpu=-1, mem=-1):
        super().__init__(name, cmd, cpu, mem)

    def append_arg(self, arg): self._cmd.append(arg)

    def set_witness_output(self, cex, cert):
        self.append_arg('--cex')
        self.append_arg(cex)
        self.append_arg('--certificate')
        self.append_arg(cert)

    def verbose(self, level):
        self.append_arg(f'--verbose')

    def set_time_limit(self, arg): self._cpu = arg
    def set_memory_limit(self, arg): self._mem = arg
    
    def __str__(self):
        return '[' + self.name + '] ' + ' '.join(self.cmd)

    def binary_certificate(self): return False

class AvyBmcConfig(SolverCfg):
    def __init__(self, name, cmd, cpu=-1, mem=-1):
        super().__init__(name, cmd, cpu, mem)

    def append_arg(self, arg): self._cmd.append(arg)

    def set_witness_output(self, cex, cert):
        self.append_arg('--cex={0}'.format(cex))

    def verbose(self, level):
        self.append_arg('--verbose={0}'.format(level))

    def set_time_limit(self, arg): self._cpu = arg
    def set_memory_limit(self, arg): self._mem = arg

    def __str__(self):
        return '[' + self.name + '] ' + ' '.join(self.cmd)

    def binary_certificate(self): return True # Or throw an error?

def profiles():
    
    profs = dict()

    def reg_profile(cfg): profs[cfg.name] = cfg

    reg_profile (SolverCfg ('avymin',
                            [getAvy (), '--reset-cover=1', '-a',
                             '--kstep=1',
                             '--shallow-push=1', '--tr0=1', '--min-suffix=1', '--incr=1',
                             '--glucose', '--glucose-inc-mode=1',
                             '--sat-simp=0', '--glucose_itp=1']))

    reg_profile (SolverCfg ('avysimp',
                            [getAvy (), '--reset-cover=1', '-a',
                             '--kstep=1',
                             '--shallow-push=1', '--tr0=1', '--min-suffix=0',
                             '--glucose', '--glucose-inc-mode=1', '--itp-simp=1', '--incr=0',
                             '--sat-simp=1', '--glucose_itp=1']))

    reg_profile (SolverCfg ('navy',
                            [getAvy (), '--reset-cover=1', '--opt-bmc=1',
                             '--kstep=1',
                             '--shallow-push=1', '--min-suffix=1', '--incr=1',
                             '--glucose', '--glucose-inc-mode=0', '--tr0=1',
                             '--sat-simp=1', '--glucose_itp=1']))

    reg_profile (SolverCfg ('abcpdr', [getAbcPdr()]))

    reg_profile (AvyBmcConfig ('fib', [getAvyBmc(), '--opt-bmc', '--incr', '--glucose', '--depth=1000', '--glucose-inc-mode']))

    reg_profile (SolverCfg ('kavy1',
                            [getAvy (), '--coi=1', '--incr=1', '--sat-simp=1', '--tr0=1',
                             '--itp-simp=0', '--shallow-push=1', '--reset-cover=1',
                             '--glucose', '--glucose_itp', '--opt-bmc=0',
                             '--quip=0', '--commitAbs=0', '--lemma-abs=1',
                             '--kind-pol=1', '--suffixSA=1', '-a']))

    reg_profile (SolverCfg ('kavy2',
                            [getAvy (), '--coi=1', '--incr=1', '--sat-simp=1', '--tr0=1',
                             '--itp-simp=0', '--shallow-push=1', '--reset-cover=1',
                             '--glucose', '--glucose_itp', '--opt-bmc=0',
                             '--quip=0', '--commitAbs=0', '--lemma-abs=1',
                             '--kind-pol=2']))

    reg_profile (SolverCfg ('kavy3',
                            [getAvy (), '--coi=1', '--incr=1', '--sat-simp=1', '--tr0=1',
                             '--itp-simp=0', '--shallow-push=1', '--reset-cover=1',
                             '--glucose', '--glucose_itp', '--opt-bmc=0',
                             '--quip=0', '--commitAbs=0', '--lemma-abs=1',
                             '--kind-pol=1']))

    # cadical1: incremental, [pre/in]processing, minimization
    reg_profile(SolverCfg('Macallan',
                          [getAvy(),
                            '--shallow-push=1',
                            '--min-core=1',
                            '--coi=1',
                            '--tr0=1',
                            '--min-suffix=1',
                            '--incr=1',
                            '--cadical_itp=1',
                            '--cadical_itp_inprocessing=1',
                            '--itp-simp=1',
                            '--cadical_itp_minimize=1',
                            '--cadical_itp_minimizer_inprocessing=1']))

    # cadical2: incremental, [pre/in]processing
    reg_profile(SolverCfg('JohnnieWalker',
                          [getAvy(),
                            '--shallow-push=1',
                            '--min-core=1',
                            '--coi=1',
                            '--tr0=1',
                            '--min-suffix=1',
                            '--incr=1',
                            '--cadical_itp=1',
                            '--cadical_itp_inprocessing=1',
                            '--itp-simp=1',
                            '--cadical_itp_minimize=0',
                            '--cadical_itp_minimizer_inprocessing=1']))

    # cadical3: incremental, minimization
    reg_profile(SolverCfg('Jameson',
                          [getAvy(),
                            '--shallow-push=1',
                            '--min-core=1',
                            '--coi=1',
                            '--tr0=1',
                            '--min-suffix=1',
                            '--incr=1',
                            '--cadical_itp=1',
                            '--cadical_itp_inprocessing=0',
                            '--itp-simp=0',
                            '--cadical_itp_minimize=1',
                            '--cadical_itp_minimizer_inprocessing=1']))

    # cadical4: [pre/in]processing
    reg_profile(SolverCfg('Glenlivet',
                          [getAvy(),
                            '--shallow-push=1',
                            '--min-core=1',
                            '--coi=1',
                            '--tr0=1',
                            '--min-suffix=1',
                            '--incr=0',
                            '--cadical_itp=1',
                            '--cadical_itp_inprocessing=1',
                            '--itp-simp=1',
                            '--cadical_itp_minimize=0',
                            '--cadical_itp_minimizer_inprocessing=1']))

    reg_profile(RfvConfig('RFVEV', [getRfv(), '-e']))

    reg_profile(RfvConfig('RFV', [getRfv()]))
    return profs

def list_profiles(option, opt_str, value, parser):
    for p in profiles().values():  # Changed itervalues() to values() for Python 3
        print(str(p))
    sys.exit(0)

def parseOpt(argv):
    from optparse import OptionParser

    parser = OptionParser()
    parser.add_option('--list-profiles', action="callback",
                      callback=list_profiles,
                      help='(INTERNAL USE ONLY) List all available profiles')
    parser.add_option('-p', '--profiles', type=str,
                      default='navy:abcpdr:fib:kavy1:kavy3:Macallan:JohnnieWalker:Jameson:RFVEV:RFV', help='Colon separated list of profiles to run')
    parser.add_option("--save-temps", dest="save_temps",
                      help="Do not delete the temporary directory holding intermediate files",
                      action="store_true",
                      default=False)
    parser.add_option("--verbose", dest="verbose",
                      action="store_true",
                      default=False, help="(INTERNAL USE ONLY) Print verbose output")
    parser.add_option("--temp-dir", dest="temp_dir",
                      help="Temporary directory to store intermediate files",
                      default=None)
    parser.add_option('--pp-cpu', dest='pp_cpu',
                      help='(INTERNAL USE ONLY) CPU time limit (seconds) for pre-processing',
                      type=int, default=120)
    parser.add_option('--cex', type=str, default='cex', help='Counterexample filename')
    parser.add_option('--certificate', type=str, default='certificate', help='Certificate filename without extension (extension will be added based on the solver)')
    parser.add_option("--check-witness", dest="check_witness",
                      action="store_true",
                      default=False, help="(INTERNAL USE ONLY) verify the witness")
    parser.add_option("--exit-on-error", dest="exit_on_error",
                      action="store_true",
                      default=False, help="(INTERNAL USE ONLY) exit if some engine crashes")
    parser.add_option("--dedicated", dest="dedicated",
                      action="store_true",
                      default=False, help="(INTERNAL USE ONLY) run each engine on a dedicated core")
    parser.add_option('--cpu', type='int', dest='cpu',
                      help='(INTERNAL USE ONLY) CPU time limit (seconds) TEMP: has no effect',
                      default=-1)
    parser.add_option('--mem', type='int', dest='mem',
                      help='(INTERNAL USE ONLY) MEM limit (MB) TEMP: has no effect', default=-1)

    (options, args) = parser.parse_args(argv)

    return (options, args)

def createWorkDir(opt):
    if opt.temp_dir is None:
        workdir = tempfile.mkdtemp(prefix='avy-')
    else:
        workdir = opt.temp_dir
    if opt.verbose: print("Working directory", workdir)
    if not opt.save_temps: atexit.register(shutil.rmtree, path=workdir)
    return workdir

def getPyPath(script):
    fn = os.path.join(root, script)
    if not isexec(fn): raise IOError("Cannot find " + script)
    return fn

def isexec(fpath):
    if fpath is None: return False
    return os.path.isfile(fpath) and os.access(fpath, os.X_OK) 

def cat(in_file, out_file): out_file.write(in_file.read())

def which(program):
    fpath, fname = os.path.split(program)
    if fpath:
        if isexec(program):
            return program
    else:
        for path in os.environ["PATH"].split(os.pathsep):
            exe_file = os.path.join(path, program)
            if isexec(exe_file):
                return exe_file
    return None

def runPP(workdir, in_name, cpu=-1, verbose=False):
    '''pre-processing '''
    if verbose: print("[pavy] in_name = ", in_name)

    out_name = os.path.basename(in_name)
    out_name, ext = os.path.splitext(out_name)
    out_name = os.path.join(workdir, out_name + '_pp' + ext)
    
    # abc_args = [getAbc(),
    #             '-c',
    #             '&r {x} ; &lcorr ; &scorr; &fraig ; &put; write_aiger {y}'.format(x=in_name,
    #                                                                y=out_name)]
    abc_exec_cmd = '-c' if verbose else '-q'
    abc_args = [getAbc(),
                abc_exec_cmd,
                '&r {x}; &put; fold; &get; &dc2; &fraig -C 1000; &put; write_aiger {y}'.format(x=in_name,
                                                                   y=out_name)]
    if verbose: print('[pavy]', ' '.join(abc_args))


    def _set_limits():
        if cpu > 0:
            resource.setrlimit(resource.RLIMIT_CPU, [cpu, cpu])
   
    try:
        sub.check_call(abc_args, preexec_fn=_set_limits)
    except sub.CalledProcessError as e:
        if verbose:
            print('[pavy] pre-processing failed with', e)

        abc_args = [getAbc(), abc_exec_cmd,
                    '&r {x} ; &put; write_aiger {y}'.format(x=in_name, y=out_name)]
        try:
            if verbose: print('[pavy] trivial pre-processing')
            sub.check_call(abc_args)
        except sub.CalledProcessError as e2:
            if verbose: print('[pavy] trivial pre-processing failed with', e2)
            out_name = in_name
    return out_name

def runProc(fname, engine, verbose=False, dedicated=False):
    cfg = engine['cfg']
    args = cfg.cmd
    cpu = cfg.cpu
    mem = cfg.mem
    stdout = engine['stdout']
    stderr = engine['stderr']

    args += [fname]

    if dedicated:
        core = engine['core']
        args = ["taskset", "-c", str(core)] + args

    def _set_limits():
        if mem > 0:
            mem_bytes = mem * 1024 * 1024
            resource.setrlimit(resource.RLIMIT_AS, [mem_bytes, mem_bytes])
        if cpu > 0:
            resource.setrlimit(resource.RLIMIT_CPU, [cpu, cpu])

    p = sub.Popen(args,
                     stdout=open(stdout, 'w'),
                     stderr=open(stderr, 'w'),
                     preexec_fn=_set_limits)

    if verbose: print(f"[pavy] kicking off [{cfg.name}] in {p.pid}: {' '.join(args)}")
    engine['pid'] = p.pid
    return p

def getAvy():
    avy = which("avy")
    if avy is None: 
        raise IOError("Cannot find avy")
    return avy

def getAvyBmc():
    avybmc = which("avybmc")
    if avybmc is None:
        raise IOError("Cannot find avybmc")
    return avybmc

def getAbc():
    abc = which('abc')
    if abc is None:
        raise IOError('Cannot find abc')
    return abc

def getAbcPdr():
    f = which('abcpdr')
    if f is None:
        raise IOError('Cannot find abcpdr')
    return f

def getRfv():
    f = which('rfv')
    if f is None:
        raise IOError('Cannot find rfv')
    return f

def getUninitializedMapper():
    f = which('unintitialized_mapping')
    if f is None:
        raise IOError('Cannot find unintitialized_mapping')
    return f

def getAig2Aig():
    f = which('aigtoaig')
    if f is None:
        raise IOError('Cannot find aigtoaig')
    return f

def getCertChecker():
    return os.path.join(script_dir, '../certifaiger/build/check')

def getCexChecker():
    return os.path.join(script_dir, '../certifaiger/build/aiger/aigsim')

def execute (cmd):
    try:
        result = sub.run(cmd, check=True, shell=True, stdout=sub.PIPE, stderr=sub.PIPE)
        return True, result.stdout.decode()
    except sub.CalledProcessError as e:
        return False, e.stdout.decode()
        # pass

def create_uninitialized_mapping(workdir, fname, verbose):
    mapping_fname = os.path.join(workdir, os.path.basename(fname) + '.map')
    cmd = f"{getUninitializedMapper()} {fname} {mapping_fname}"
    if verbose: print('[pavy] creating uninitialized mapping with', cmd)
    execute(cmd)
    return mapping_fname

def cert_mapping(cert, mapping_fname, binary, verbose):
    if verbose: print('[pavy] adding mapping to certificate')
    fname = cert.split(".")[0]
    if binary:
        cmd = f"{getAig2Aig()} {cert} {fname}.aag"
        if verbose: print('[pavy] creating aag certificate', cmd)
        execute(cmd)
    cert = f"{fname}.aag"
    with open(cert, 'r') as f:
        lines = f.readlines()
        found = False
        with open(cert, 'w') as f:
            for line in lines:
                if (found == False and len(line.strip()) == 1 and line == "c\n"):
                    found = True
                    with open(mapping_fname, 'r') as m:
                        f.write(m.read())
                f.write(line)
        f.close()

    return cert

def check_certificate(model, cert, verbose):
    cmd = f"{getCertChecker()} {model} {cert}"
    if verbose: print('[pavy] checking certificate with', cmd)
    res, out = execute(cmd)
    if 'Error: Certificate check failed' in out:
        print ("[pavy] Certificate check failed")
        return False
    elif 'Success: Certificate check passed' in out:
        print ("[pavy] Certificate check passed")
        return True
    assert (False and "Unexpected output")

def check_cex(model, cex, verbose):
    cmd = f"{getCexChecker()} -w {model} {cex}"
    if verbose: print('[pavy] checking cex with', cmd)
    res, out = execute(cmd)
    if 'Trace is a witness for: { }' in out:
        print ("[pavy] Cex check failed")
        return False
    elif 'Trace is a witness for: { b0 }' in out:
        print ("[pavy] Cex check passed")
        return True
    assert (False and "Unexpected output")

def report_winner(model, model_pp, code, engine, opt, mapping):

    def of(n):
        if n == '-': return sys.stdout
        else: return open(n, 'w')

    def add_cert_ext(fname, binary):
        if binary: return f"{fname}.aig"
        else : return f"{fname}.aag"

    wcfg = engine['cfg']

    if opt.verbose:
        cat(open(engine['stdout']), sys.stdout)
        cat(open(engine['stdout']), sys.stderr)
        print('[pavy] Witness begin')

    cert_name = opt.certificate

    if code == 1:
        aig.adjust_cex(in_cex=open(engine['cex']),
                        cex_aig=aig.parse(open(model_pp, 'rb')),
                        orig_aig=aig.parse(open(model, 'rb')),
                        out_cex=of(opt.cex))
        assert (not opt.check_witness or check_cex(model, opt.cex, opt.verbose))
    elif code == 0:
        cert_name = add_cert_ext(cert_name, wcfg.binary_certificate())
        shutil.copy2(engine['cert'], cert_name)
        cert_name = cert_mapping(cert_name, mapping, wcfg.binary_certificate(), opt.verbose)
        # assert (not opt.check_witness or check_certificate(model, cert_name, opt.verbose))

    if opt.verbose: print('[pavy] Witness end')
    print('Winner: ', wcfg.name)
    print('Result:  ' + ('SAFE' if code == 0 else 'UNSAFE'))
    print('Witness: ' + (cert_name if code == 0 else opt.cex))

def run(workdir, fname, profs, opt):
    '''Run everything and wait for an answer'''

    if len(profs) == 0: return

    print("[pavy] starting run with fname={f}".format(f=fname))
    sys.stdout.flush()

    if opt.verbose: print("[pavy] running pp")
    pp_name = runPP(workdir, fname, cpu=opt.pp_cpu, verbose=opt.verbose)
    if opt.verbose: print("[pavy] finished pp, output={f}".format(f=pp_name))

    p = profiles()
    available_cores = list(os.sched_getaffinity(0))
    dedicated = opt.dedicated and len(profs) + 1 <= len(available_cores)

    engines = {}
    for x in profs:
        cfg = p[x]
        engines[x] = {'cfg': cfg, 'stdout': os.path.join(workdir, cfg.name + '_avy{0}.stdout'.format(x)),
                   'stderr': os.path.join(workdir, cfg.name + '_avy{0}.stderr'.format(x)),
                   'cex': os.path.join(workdir, cfg.name + '_avy{0}.cex'.format(x)),
                   'cert': os.path.join(workdir, cfg.name + '_avy{0}.cert'.format(x))}
        if opt.verbose: cfg.verbose(1)
        cfg.set_witness_output(engines[x]['cex'], engines[x]['cert'])
        cfg.set_time_limit(opt.cpu)
        cfg.set_memory_limit(opt.mem)
        if dedicated:
            engines[x]['core'] = available_cores[0]
            available_cores.remove(available_cores[0])

    uninitialized_mapping = create_uninitialized_mapping(workdir, fname, opt.verbose)

    global running
    running.extend([runProc(pp_name, engines[e], verbose=opt.verbose, dedicated=dedicated) for e in engines])

    pids = [p.pid for p in running]
    print(f"[pavy] running: {pids}")

    pid = -1
    exit_code = 2
    sig = -1
    returnvalue = -1
    errors = False

    while len(pids) != 0:
        try:
            (pid, returnvalue, ru_child) = os.wait4(-1, 0)
        except OSError:  # probably got interrupted
            break
        (exit_code, sig) = (returnvalue // 256, returnvalue % 256) 

        if opt.verbose or exit_code != 0 or sig != 0:
            if sig == 9:
                print(f"[pavy] killed pid {pid} due to timeout")
            else:
                print(f"[pavy] finished pid {pid} with code {exit_code} and signal {sig}")

        pids.remove(pid)
        
        # exit codes: 0 = SAFE, 1 = UNSAFE, 2 = UNKNOWN, 3 = validation error
        if sig == 0 and (exit_code == 0 or exit_code == 1):
            winner = next((n for n, e in engines.items() if e['pid'] == pid), None)
            report_winner(model=fname, model_pp=pp_name, code=exit_code, engine=engines[winner], opt=opt, mapping=uninitialized_mapping)
            for p in pids:
                try:
                    if opt.verbose: print("[pavy] trying to kill ", p)
                    os.kill(p, signal.SIGTERM)
                except OSError: pass
                finally:
                    try:
                        if opt.verbose: print("[pavy] waiting for ", p)
                        os.waitpid(p, 0)
                    except OSError: pass
            break
        elif (sig != 9):
            errors = True
    
    if sig != 0 or (exit_code != 0 and exit_code != 1):
        if opt.verbose:
            for e in engines.values():
                print('[pavy] LOG BEGIN', cfg.name)
                cat(open(e['stdout']), sys.stdout)
                cat(open(e['stderr']), sys.stderr)
                print('[pavy] LOG END', e['cfg'].name)
        if errors:
            print("[pavy] Some engines have failed")
            if opt.exit_on_error:
                print('[pavy] Calling sys.exit with {0}'.format(returnvalue // 256))
                sys.exit(returnvalue // 256)

        print('[pavy] Winner: Unknown')
        print('[pavy] Result: UNDETERMINED')

    running[:] = []
    return exit_code

def main(argv):
    os.setpgrp()

    (opt, args) = parseOpt(argv[1:])

    workdir = createWorkDir(opt)
    returnvalue = 0
    for fname in args:
        returnvalue = run(workdir, fname=fname, profs=opt.profiles.split(':'), opt=opt)
    return returnvalue

def killall():
    global running
    for p in running:
        try:
            if p.poll() is None:
                p.terminate()
                p.kill()
                p.wait()
        except OSError: pass
    running[:] = []

if __name__ == '__main__':
    sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', buffering=1)
    script_dir = os.path.dirname(os.path.realpath(__file__))
    os.environ['PATH'] = os.path.join(script_dir, f'/home/{os.environ['LOGNAME']}/for-pavy') + os.pathsep + os.environ['PATH']

    try:
        signal.signal(signal.SIGTERM, lambda x, y: killall())
        sys.exit(main(sys.argv))
    except KeyboardInterrupt: pass
    finally: killall()
