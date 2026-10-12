"""Compile and run an unchanged Lean regression client with fresh dependencies.
This is a test backend, not an implementation of the controlled machine.
All artifacts persist outside the repository. No project C is ever overwritten.
"""
from __future__ import annotations
import hashlib, json, os, re, shutil, signal, subprocess, tempfile, time
from pathlib import Path

class NativeClientError(ValueError):
    pass

def _sha(path, lf=False):
    data = Path(path).read_bytes()
    return hashlib.sha256(data.replace(b'\r\n', b'\n') if lf else data).hexdigest()

def _json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')

def _module_path(base, name, suffix):
    return base.joinpath(*name.split('.')).with_suffix(suffix)

class _NativeClient:
    def __init__(self, root, source, audits, done, runtime_timeout, archive):
        self.out = archive
        self.root = Path(root).resolve()
        self.source, self.audits, self.done = source, sorted(audits), done
        self.runtime_timeout = runtime_timeout
        self.phases, self.inputs, self.order, self.modules, self.core = [], {}, [], {}, {}
        self.protocol = {'schema': 'documentary-native-client-v1', 'qualification': False,
          'prepared_before_first_subprocess': True, 'workspace': str(self.root),
          'client_sha256': hashlib.sha256(source).hexdigest(),
          'expected_elaboration_audits': sorted(audits), 'expected_runtime_stdout_hex': done.hex(),
          'runtime_timeout_seconds': runtime_timeout, 'status': 'PREFLIGHT',
          'client_compiler_options': ['-Dcompiler.extract_closed=false'],
          'client_compiler_option_scope': 'Only client generation; project module generation and guarded C unchanged',
          'rule': 'Same client bytes, fresh project olean+C, exact guarded C comparison, separate audits/runtime, no cache, preserve all raw logs; any rejection fails.'}
        # A protocol exists before reading project inputs or launching anything.
        _json(self.out/'protocol-preflight.json', self.protocol)
        (self.out/'Smoke.lean').write_bytes(source)
        self.capture(self.out/'Smoke.lean')
        self.capture(Path(__file__))

    def capture(self, path, lf=False):
        path = Path(path).resolve()
        if str(path) in self.inputs:
            if self.inputs[str(path)]['lf'] != lf:
                raise NativeClientError('Conflicting normalization for input: '+str(path))
            return path
        self.inputs[str(path)] = {'sha256': _sha(path, lf), 'lf': lf}
        with (self.out/'input-records.jsonl').open('a',encoding='utf-8') as records:
            records.write(json.dumps({'path':str(path),**self.inputs[str(path)]})+'\n')
        return path

    def differences(self):
        result = []
        for name, expected in self.inputs.items():
            try:
                actual = _sha(name, expected['lf'])
                if actual != expected['sha256']:
                    result.append({'path': name, 'expected': expected['sha256'], 'actual': actual})
            except BaseException as error:
                result.append({'path': name, 'expected': expected['sha256'], 'error': repr(error)})
        return result

    def unchanged(self):
        differences = self.differences()
        if differences: raise NativeClientError('Input changes: '+repr(differences))

    def phase(self, name, args, timeout):
        directory = self.out/'raw'/name
        directory.mkdir(parents=True, exist_ok=False)
        command = [str(x) for x in args]
        launched = {'command': command, 'cwd': str(self.root), 'started_unix': time.time(),
          'pid': None, 'timeout_seconds': timeout}
        _json(directory/'start.json', launched)
        started = time.perf_counter()
        process, timed_out, cleanup, error = None, False, None, None
        try:
            with (directory/'stdout.log').open('wb') as out, (directory/'stderr.log').open('wb') as err:
                process = subprocess.Popen(command, cwd=self.root, stdout=out, stderr=err,
                  start_new_session=(os.name == 'posix'))
                launched['pid'] = process.pid
                launched['owned_pgid'] = process.pid if os.name == 'posix' else None
                launched['new_process_session'] = os.name == 'posix'
                _json(directory/'start.json', launched)
                try: process.wait(timeout=timeout)
                except subprocess.TimeoutExpired:
                    timed_out = True
                    cleanup = self.cleanup(process, directory)
        except BaseException as caught:
            error = repr(caught)
            # An exception after Popen may leave this phase's owned child live.
            # Preserve the original phase error and clean only that child/group.
            if process is not None and process.poll() is None:
                try:
                    cleanup = self.cleanup(process, directory)
                except BaseException as cleanup_error:
                    cleanup = {'owned_pid': process.pid, 'confirmed': False,
                      'error': repr(cleanup_error), 'owned_parent_exit_code': process.poll()}
                _json(directory/'exception-cleanup-result.json', cleanup)
                if not cleanup.get('confirmed', False):
                    error += '; owned process cleanup unconfirmed'
        finally:
            result = {'name': name, 'command': command, 'pid': process.pid if process else None,
              'exit_code': process.poll() if process else None, 'timed_out': timed_out,
              'phase_error': error, 'elapsed_seconds': time.perf_counter()-started,
              'cleanup': cleanup,
              'raw_log_snapshot_final': process is not None and process.poll() is not None}
            for file in ['stdout.log','stderr.log']:
                path = directory/file
                if path.exists():
                    result[file] = {'bytes': path.stat().st_size, 'sha256': _sha(path)}
                else: result[file] = {'missing': True}
            _json(directory/'result.json', result)
            self.phases.append(result)
            _json(self.out/'phase-results.json', self.phases)
        if error or timed_out or result['exit_code'] != 0:
            raise NativeClientError('Phase rejected: '+name+'; raw artifacts: '+str(directory))
        return (directory/'stdout.log').read_bytes(), (directory/'stderr.log').read_bytes()

    def cleanup(self, process, directory):
        result = {'owned_pid': process.pid, 'confirmed': False, 'error': None}
        if os.name == 'posix':
            # Popen(start_new_session=True) created this exact group. Never use
            # the caller's group or a group inherited from the surrounding gate.
            group = process.pid
            result.update({'owned_pgid':group,'created_by_phase':True,'signals':[]})
            def exists():
                try:
                    os.killpg(group,0)
                    return True
                except ProcessLookupError: return False
            try:
                try:
                    os.killpg(group,signal.SIGTERM)
                    result['signals'].append('SIGTERM')
                except ProcessLookupError:
                    result['group_absent_before_signal'] = True
                try: process.wait(timeout=30)
                except subprocess.TimeoutExpired:
                    result['parent_term_wait_timeout'] = True
                if exists():
                    try:
                        os.killpg(group,signal.SIGKILL)
                        result['signals'].append('SIGKILL')
                    except ProcessLookupError: pass
                try: process.wait(timeout=5)
                except BaseException as caught: result['owned_parent_wait_error'] = repr(caught)
                # A reaped parent alone is insufficient: inspect its owned group.
                for _ in range(50):
                    if not exists(): break
                    time.sleep(0.1)
                result['group_absent_after_cleanup'] = not exists()
                result['owned_parent_exit_code'] = process.poll()
                result['confirmed'] = (result['group_absent_after_cleanup'] and process.poll() is not None)
            except BaseException as caught:
                result['error'] = repr(caught)
                result['owned_parent_exit_code'] = process.poll()
            finally:
                _json(directory/'cleanup-result.json',result)
            return result
        if os.name != 'nt':
            result['error'] = 'Unsupported host; owned process cleanup unconfirmed'
            _json(directory/'cleanup-result.json',result)
            return result
        command = ['taskkill','/PID',str(process.pid),'/T','/F']
        result['command'] = command
        killer = None
        try:
            with (directory/'cleanup-stdout.log').open('wb') as out, (directory/'cleanup-stderr.log').open('wb') as err:
                killer = subprocess.Popen(command, stdout=out, stderr=err)
                result['taskkill_pid'] = killer.pid
                try: killer.wait(timeout=30)
                except subprocess.TimeoutExpired:
                    result['error'] = 'taskkill timeout; owned tree cleanup unconfirmed'
                    killer.kill()
                    try: killer.wait(timeout=5)
                    except BaseException as caught: result['taskkill_stop_error'] = repr(caught)
                result['taskkill_exit_code'] = killer.poll()
            try: process.wait(timeout=30)
            except BaseException as caught: result['owned_parent_wait_error'] = repr(caught)
            result['owned_parent_exit_code'] = process.poll()
            result['confirmed'] = (result['taskkill_exit_code'] == 0 and process.poll() is not None and result['error'] is None)
        except BaseException as caught:
            result['error'] = repr(caught)
            result['owned_parent_exit_code'] = process.poll()
        finally:
            for file in ['cleanup-stdout.log','cleanup-stderr.log']:
                if (directory/file).exists(): result[file+'_sha256'] = _sha(directory/file)
            _json(directory/'cleanup-result.json', result)
        return result

    def discover(self):
        if os.name not in ('nt','posix'): raise NativeClientError('Unsupported native regression host')
        for relative in ['lean-toolchain','lakefile.toml','lake-manifest.json',
                         'scripts/run-documentary-expanded-control-smoke.py']:
            self.capture(self.root/relative)
        version_text = (self.root/'lean-toolchain').read_text(encoding='utf-8').strip()
        match = re.fullmatch(r'leanprover/lean4:v([0-9]+\.[0-9]+\.[0-9]+)', version_text)
        if not match: raise NativeClientError('Unsupported pinned toolchain specification: '+version_text)
        self.expected_version = match.group(1)
        roots = re.findall(r'^import\s+(\S+)\s*$', self.source.decode('utf-8'), re.M)
        if not roots: raise NativeClientError('Client has no explicit module imports')
        visiting = set()
        def visit(name):
            if name in self.modules: return
            if name in visiting: raise NativeClientError('Import cycle: '+name)
            visiting.add(name)
            source = self.capture(_module_path(self.root,name,'.lean'))
            setup_path = self.capture(_module_path(self.root/'.lake/build/ir',name,'.setup.json'))
            old_c = self.capture(_module_path(self.root/'.lake/build/ir',name,'.c'))
            trace = self.capture(_module_path(self.root/'.lake/build/lib/lean',name,'.trace'))
            setup = json.loads(setup_path.read_text(encoding='utf-8'))
            if setup['name'] != name or setup.get('isModule') != False or setup.get('plugins') or setup.get('dynlibs'):
                raise NativeClientError('Unexpected module/plugin/dynlib setup: '+name)
            for imp, groups in sorted(setup['importArts'].items()):
                if _module_path(self.root,imp,'.lean').exists(): visit(imp)
                else:
                    for group in groups:
                        for artifact in group: self.core[str(self.capture(artifact))] = True
            self.modules[name] = {'source': str(source), 'setup': setup,
              'old_c': str(old_c), 'old_c_sha256': _sha(old_c), 'trace': str(trace)}
            visiting.remove(name)
            self.order.append(name)
        for name in roots: visit(name)
        lake = shutil.which('lake')
        if not lake: raise NativeClientError('lake not found in the received environment')
        self.lake = self.capture(lake)
        _json(self.out/'protocol-before-prefix-preflight.json',{
          **self.protocol,'phase':'toolchain-prefix-discovery',
          'inputs_before_first_popen':self.inputs,'lean_toolchain':version_text,
          'module_metadata':self.modules,'module_order':self.order,
          'implicit_core_artifacts_not_assumed_present_in_importArts':True})
        stdout,stderr = self.phase('received-prefix',[self.lake,'env','lean','--print-prefix'],30)
        if stderr or not stdout.strip(): raise NativeClientError('Received prefix query failed')
        self.prefix = Path(stdout.decode('utf-8').strip()).resolve()
        if not (self.prefix/'lib/lean').is_dir(): raise NativeClientError('Received prefix has no core library')
        for artifact in self.core:
            if not Path(artifact).resolve().is_relative_to(self.prefix/'lib/lean'):
                raise NativeClientError('Unclassified external import artifact: '+artifact)
        # Legacy setups can omit every implicit core import. Fix the whole core
        # artifact set conservatively before compiling any project module.
        self.implicit_core_artifacts = {}
        for path in sorted((self.prefix/'lib/lean').rglob('*')):
            if path.is_file() and ('.olean' in path.name or path.name.endswith(('.ir','.ir.sig'))):
                received = self.capture(path)
                self.implicit_core_artifacts[str(received)] = self.inputs[str(received)]['sha256']
        if not self.implicit_core_artifacts:
            raise NativeClientError('No implicit core artifacts captured')
        suffix = '.exe' if os.name == 'nt' else ''
        self.native_executable_name = 'Smoke'+suffix
        self.received_tools = {}
        for name in ['lean','leanc','lake']:
            path = self.capture(self.prefix/'bin'/(name+suffix))
            self.received_tools[name] = str(path)
        # Windows ships clang/lld here; POSIX toolchains may receive host tools.
        # Record available candidates and the actual leanc --version response.
        for name in ['clang','ld.lld','cc']:
            bundled = self.prefix/'bin'/(name+suffix)
            received = str(bundled) if bundled.exists() else shutil.which(name)
            if received:
                self.received_tools[name] = str(self.capture(received))
        config = self.capture(self.prefix/'src/lean/lake/Lake/Config/LeanConfig.lean')
        config_text = config.read_text(encoding='utf-8')
        declarations = list(re.finditer(r'^public def leancArgs\s*:\s*BuildType\s*→\s*Array String\s*\n((?:^\|[^\n]*\n)+)',config_text,re.M))
        if len(declarations) != 1:
            raise NativeClientError('Cannot identify exactly one BuildType.leancArgs declaration')
        self.release_declaration = declarations[0].group(0)
        release = re.search(r'^\|\s*\.?release\s*=>\s*#\[(.*?)\]\s*$',declarations[0].group(1),re.M)
        if not release: raise NativeClientError('Cannot derive release case inside BuildType.leancArgs')
        self.release_flags = re.findall(r'"([^"\\]*)"',release.group(1))
        if not self.release_flags: raise NativeClientError('Received release flags are empty')
        for path in sorted((self.prefix/'lib').rglob('*.a')): self.capture(path)
        for path in sorted((self.prefix/'include').rglob('*.h')): self.capture(path)
        for path in sorted((self.prefix/'bin').glob('*.dll')): self.capture(path)
        if os.name == 'posix':
            for path in sorted((self.prefix/'lib').rglob('*.so*')):
                if path.is_file(): self.capture(path)
        self.protocol.update({'status': 'PREPARED', 'project_modules': self.order,
          'module_count': len(self.order), 'module_metadata': self.modules,
          'toolchain_prefix_from_received_query': str(self.prefix), 'lean_toolchain': version_text,
          'host_process_policy': 'owned new session/group per phase on POSIX; taskkill owned PID tree on Windows',
          'received_tools': self.received_tools,
          'implicit_core_artifacts_sha256': self.implicit_core_artifacts,
          'environment_received': {name:os.environ.get(name) for name in ['CC','CXX','LEAN_CC','LEAN_SYSROOT','LEAN_PATH','LEAN_SRC_PATH','PATH']},
          'platform_qualification': 'Windows external protocol is measured separately; POSIX support is implemented but not qualified by a Windows run',
          'release_flags_received': self.release_flags, 'source_of_release_flags': str(config),
          'release_flags_declaration': self.release_declaration,
          'toolchain_and_core_inputs': self.inputs,
          'phase_timeouts_seconds': {'module_generation': 900,'client_generation': 900,
            'object_compilation': 300,'link': 900,'runtime': self.runtime_timeout},
          'stop_rule': 'No refreshed guarded hashes; C differences stop before native compilation.',
          'trust_boundary': 'Pinned Lean compiler/C emitter, leanc/clang and core runtime; no compiler-correctness theorem is claimed.'})
        _json(self.out/'protocol-before-tool-validation.json', self.protocol)
        _json(self.out/'inputs-preflight.json',self.inputs)
        self.unchanged()
        stdout, stderr = self.phase('received-version',[self.lake,'env','lean','--version'],30)
        if stderr or ('version '+self.expected_version+',') not in stdout.decode('utf-8'):
            raise NativeClientError('Received Lean version differs from pin')
        compiler_stdout, compiler_stderr = self.phase('received-compiler',[self.lake,'env','leanc','--version'],30)
        if compiler_stderr or not compiler_stdout: raise NativeClientError('Received compiler identification failed')
        self.protocol['leanc_version_stdout'] = compiler_stdout.decode('utf-8')
        self.protocol['version_stdout'] = (self.out/'raw/received-version/stdout.log').read_text(encoding='utf-8')
        _json(self.out/'protocol-before-generation.json', self.protocol)

    def retarget(self, setup):
        # JSON roundtrip copies nested arrays without mutating original metadata.
        result = json.loads(json.dumps(setup))
        for name, groups in result['importArts'].items():
            if name not in self.modules: continue
            if len(groups) != 1 or len(groups[0]) != 1 or not groups[0][0].endswith('.olean'):
                raise NativeClientError('Unexpected legacy project artifact format: '+name)
            groups[0][0] = str(_module_path(self.out/'olean',name,'.olean'))
        return result

    def elaborate(self):
        generated = []
        union = {}
        for index, name in enumerate(self.order):
            module = self.modules[name]
            c = _module_path(self.out/'ir',name,'.c')
            olean = _module_path(self.out/'olean',name,'.olean')
            setup = _module_path(self.out/'setup',name,'.setup.json')
            c.parent.mkdir(parents=True,exist_ok=True)
            olean.parent.mkdir(parents=True,exist_ok=True)
            _json(setup,self.retarget(module['setup']))
            self.capture(setup)
            stdout, stderr = self.phase('generate-%03d'%index,
              [self.lake,'env','lean',module['source'],'-o',olean,'-c',c,'--setup',setup],900)
            if stderr or b'error:' in stdout.lower() or b'sorryAx' in stdout or b'depends on axioms' in stdout:
                raise NativeClientError('Module elaboration rejected: '+name)
            if _sha(c) != module['old_c_sha256']:
                _json(self.out/'c-comparison-rejected.json', {'module': name,
                  'guarded': module['old_c_sha256'], 'fresh': _sha(c),
                  'status': 'STOP_BEFORE_NATIVE_COMPILATION_REVIEW_REQUIRED'})
                raise NativeClientError('Fresh C differs from guarded C: '+name)
            self.capture(c)
            self.capture(olean)
            generated.append({'module': name,'c_sha256':_sha(c),'olean_sha256':_sha(olean),
              'source_sha256':_sha(module['source']),'setup_sha256':_sha(setup),
              'guarded_c_equal_byte_for_byte': True})
            _json(self.out/'generation-evidence.json',generated)
            union.update(module['setup']['importArts'])
        for name in re.findall(r'^import\s+(\S+)\s*$',self.source.decode('utf-8'),re.M):
            union[name] = [[str(_module_path(self.out/'olean',name,'.olean'))]]
        setup = self.out/'Smoke.setup.json'
        _json(setup,self.retarget({'name':'Smoke','package':None,'isModule':False,'imports':None,
          'dynlibs':[],'plugins':[],'options':{},'importArts':union}))
        self.capture(setup)
        validator = self.out/'ValidateSetup.lean'
        validator_source = """import Lean.Setup

def main : IO Unit := do
  let expected : Lean.ModuleSetup := { name := `Smoke }
  let loaded ← Lean.ModuleSetup.load (System.FilePath.mk CLIENT_SETUP_PATH)
  if loaded.name != expected.name || loaded.package?.isSome || loaded.isModule ||
      loaded.imports?.isSome || loaded.dynlibs.size != 0 || loaded.plugins.size != 0 then
    throw (IO.userError "Client ModuleSetup differs from declared legacy schema")
""".replace('CLIENT_SETUP_PATH',json.dumps(str(setup).replace('\\','/')))
        validator.write_text(validator_source,encoding='utf-8')
        self.capture(validator)
        stdout,stderr = self.phase('validate-client-setup',[self.lake,'env','lean','--run',validator],120)
        if stdout or stderr: raise NativeClientError('Official client setup decoder diagnostics rejected')
        stdout, stderr = self.phase('generate-client',[self.lake,'env','lean','-Dcompiler.extract_closed=false',self.out/'Smoke.lean',
          '-o',self.out/'Smoke.olean','-c',self.out/'Smoke.c','--setup',setup],900)
        lines = stdout.decode('utf-8').replace('\r\n','\n').splitlines()
        if stderr or sorted(lines) != self.audits or len(lines) != len(self.audits):
            raise NativeClientError('Client elaboration did not produce its exact clean audit list')
        self.capture(self.out/'Smoke.c')
        self.capture(self.out/'Smoke.olean')

    def compile_and_run(self):
        objects = []
        for index,name in enumerate(self.order+['Smoke']):
            c = self.out/'Smoke.c' if name == 'Smoke' else _module_path(self.out/'ir',name,'.c')
            obj = self.out/'obj'/('%03d.o'%index)
            obj.parent.mkdir(parents=True,exist_ok=True)
            self.phase('compile-%03d'%index,[self.lake,'env','leanc',*self.release_flags,'-c',c,'-o',obj],300)
            self.capture(obj)
            objects.append(obj)
            _json(self.out/'object-evidence.json',{str(p):_sha(p) for p in objects})
        response = self.out/'objects.rsp'
        response.write_text('\n'.join('"'+str(p).replace('\\','/')+'"' for p in objects)+'\n',encoding='utf-8')
        self.capture(response)
        executable = self.out/self.native_executable_name
        self.phase('link',[self.lake,'env','leanc',*self.release_flags,'@'+str(response),'-o',executable],900)
        self.capture(executable)
        _json(self.out/'native-artifacts-before-runtime.json',{'object_count':len(objects),
          'objects':{str(p):_sha(p) for p in objects},'responsefile_sha256':_sha(response),
          'executable_sha256':_sha(executable)})
        self.unchanged()
        stdout,stderr = self.phase('runtime',[executable],self.runtime_timeout)
        if stdout.replace(b'\r\n',b'\n') != self.done or stderr:
            raise NativeClientError('Native runtime stdout/stderr differs from unchanged main expectation')
        self.unchanged()
        return {'status':'NATIVE_CLIENT_PASS','qualification':False,
          'client_sha256':hashlib.sha256(self.source).hexdigest(),
          'project_modules_fresh_c_equal':len(self.order),'clean_elaboration_audits':len(self.audits),
          'runtime_done':True,'raw_artifacts':str(self.out)}

    def run(self):
        try:
            self.discover()
            self.elaborate()
            result = self.compile_and_run()
            _json(self.out/'result.json',result)
            return result
        except BaseException as error:
            _json(self.out/'result.json',{'status':'NATIVE_CLIENT_REJECTED','qualification':False,
              'error':repr(error),'completed_phases':len(self.phases),
              'input_differences_after_failure':self.differences(),
              'raw_artifacts':str(self.out),'raw_logs_preserved':True})
            raise NativeClientError(str(error)+'; native artifacts: '+str(self.out)) from error

def run_native_client(root, source, expected_audit_lines, expected_runtime_stdout, runtime_timeout=7200):
    """One native evaluation of exactly the supplied client and expected outputs.
    Construction/preflight errors are archived before any Popen.
    """
    # Archive allocation precedes construction, so even an invalid project
    # input or constructor failure has its initial protocol and failure receipt.
    archive = Path(tempfile.mkdtemp(prefix='rp-expanded-native-'))
    _json(archive/'protocol-before-construction.json',{
      'schema':'documentary-native-preflight-v1','qualification':False,
      'workspace_received':str(root),'runtime_timeout_seconds':runtime_timeout,
      'client_sha256':hashlib.sha256(source).hexdigest(),
      'expected_elaboration_audits':list(expected_audit_lines),
      'runtime_stdout_hex':expected_runtime_stdout.hex(),
      'no_subprocess_started':True})
    execution = None
    try:
        execution = _NativeClient(root,source,expected_audit_lines,expected_runtime_stdout,runtime_timeout,archive)
        return execution.run()
    except BaseException as error:
        _json(archive/'preflight-or-run-error.json',{
          'error':repr(error),'input_differences_after_failure':execution.differences() if execution else [],
          'raw_artifacts':str(archive),'qualification':False,
          'subprocesses_started':bool(execution and execution.phases)})
        raise NativeClientError(str(error)+'; native artifacts: '+str(archive)) from error
