(function(Object){
   typeof globalThis !== "object"
   &&
    (this
      ? get()
      : (Object.defineProperty
         (Object.prototype, "_T_", {configurable: true, get: get}),
        _T_));
   function get(){
    var global = this || self;
    global.globalThis = global;
    delete Object.prototype._T_;
   }
  }
  (Object));
(js=>
     async args=>{
      "use strict";
      const
       {link, src, generated, disable_effects} = args,
       isNode = globalThis.process?.versions?.node,
       math =
         {cos: Math.cos,
          sin: Math.sin,
          tan: Math.tan,
          acos: Math.acos,
          asin: Math.asin,
          atan: Math.atan,
          cosh: Math.cosh,
          sinh: Math.sinh,
          tanh: Math.tanh,
          acosh: Math.acosh,
          asinh: Math.asinh,
          atanh: Math.atanh,
          cbrt: Math.cbrt,
          exp: Math.exp,
          expm1: Math.expm1,
          log: Math.log,
          log1p: Math.log1p,
          log2: Math.log2,
          log10: Math.log10,
          atan2: Math.atan2,
          hypot: Math.hypot,
          pow: Math.pow,
          fmod: (x, y)=>x % y},
       typed_arrays =
         [Float32Array,
          Float64Array,
          Int8Array,
          Uint8Array,
          Int16Array,
          Uint16Array,
          Int32Array,
          Int32Array,
          Int32Array,
          Int32Array,
          Float32Array,
          Float64Array,
          Uint8Array,
          Uint16Array,
          Uint8ClampedArray],
       fs = isNode && require("node:fs"),
       fs_cst = fs?.constants,
       access_flags =
         fs ? [fs_cst.R_OK, fs_cst.W_OK, fs_cst.X_OK, fs_cst.F_OK] : [],
       open_flags =
         fs
          ? [fs_cst.O_RDONLY,
            fs_cst.O_WRONLY,
            fs_cst.O_RDWR,
            fs_cst.O_APPEND,
            fs_cst.O_CREAT,
            fs_cst.O_TRUNC,
            fs_cst.O_EXCL,
            fs_cst.O_NONBLOCK,
            fs_cst.O_NOCTTY,
            fs_cst.O_DSYNC,
            fs_cst.O_SYNC]
          : [];
      var
       out_channels =
         {map: new WeakMap(),
          set: new Set(),
          finalization:
          new FinalizationRegistry(ref=>out_channels.set.delete(ref))};
      function register_channel(ch){
       const ref = new WeakRef(ch);
       out_channels.map.set(ch, ref);
       out_channels.set.add(ref);
       out_channels.finalization.register(ch, ref, ch);
      }
      function unregister_channel(ch){
       const ref = out_channels.map.get(ch);
       if(ref){
        out_channels.map.delete(ch);
        out_channels.set.delete(ref);
        out_channels.finalization.unregister(ch);
       }
      }
      function channel_list(){
       return [...out_channels.set].map(ref=>ref.deref()).filter(ch=>ch);
      }
      var start_fiber;
      function make_suspending(f){
       return WebAssembly?.Suspending ? new WebAssembly.Suspending(f) : f;
      }
      function make_promising(f){
       return ! disable_effects && WebAssembly?.promising && f
               ? WebAssembly.promising(f)
               : f;
      }
      const
       decoder = new TextDecoder("utf-8", {ignoreBOM: 1}),
       encoder = new TextEncoder();
      function hash_int(h, d){
       d = Math.imul(d, 0xcc9e2d51 | 0);
       d = d << 15 | d >>> 17;
       d = Math.imul(d, 0x1b873593);
       h ^= d;
       h = h << 13 | h >>> 19;
       return (h + (h << 2) | 0) + (0xe6546b64 | 0) | 0;
      }
      function hash_string(h, s){
       for(var i = 0; i < s.length; i++) h = hash_int(h, s.charCodeAt(i));
       return h ^ s.length;
      }
      function getenv(n){
       if(isNode && globalThis.process.env[n] !== undefined)
        return globalThis.process.env[n];
       return globalThis.jsoo_env?.[n];
      }
      let record_backtrace_flag = 0;
      for(const l of getenv("OCAMLRUNPARAM")?.split(",") || []){
       if(l === "b") record_backtrace_flag = 1;
       if(l.startsWith("b=")) record_backtrace_flag = + l.slice(2) ? 1 : 0;
      }
      function alloc_stat(s, large){
       var kind;
       if(s.isFile())
        kind = 0;
       else if(s.isDirectory())
        kind = 1;
       else if(s.isCharacterDevice())
        kind = 2;
       else if(s.isBlockDevice())
        kind = 3;
       else if(s.isSymbolicLink())
        kind = 4;
       else if(s.isFIFO()) kind = 5; else if(s.isSocket()) kind = 6;
       return caml_alloc_stat
               (large,
                s.dev,
                s.ino | 0,
                kind,
                s.mode,
                s.nlink,
                s.uid,
                s.gid,
                s.rdev,
                BigInt(s.size),
                s.atimeMs / 1000,
                s.mtimeMs / 1000,
                s.ctimeMs / 1000);
      }
      const
       on_windows = isNode && globalThis.process.platform === "win32",
       call = Function.prototype.call,
       DV = DataView.prototype,
       bindings =
         {jstag:
          WebAssembly.JSTag
          || new WebAssembly.Tag({parameters: ["externref"], results: []}),
          identity: x=>x,
          from_bool: x=>! ! x,
          get: (x, y)=>x[y],
          set: (x, y, z)=>x[y] = z,
          delete: (x, y)=>delete x[y],
          instanceof: (x, y)=>x instanceof y,
          typeof: x=>typeof x,
          equals: (x, y)=>x == y,
          strict_equals: (x, y)=>x === y,
          fun_call: (f, o, args)=>f.apply(o, args),
          meth_call: (o, f, args)=>o[f].apply(o, args),
          new_array: n=>new Array(n),
          new_obj: ()=>({}),
          new: (c, args)=>new c(...args),
          global_this: globalThis,
          iter_props:
          (o, f)=>{for(var nm in o) if(Object.hasOwn(o, nm)) f(nm);},
          array_length: a=>a.length,
          array_get: (a, i)=>a[i],
          array_set: (a, i, v)=>a[i] = v,
          read_string: l=>decoder.decode(new Uint8Array(buffer, 0, l)),
          read_string_stream:
          (l, stream)=>
             decoder.decode(new Uint8Array(buffer, 0, l), {stream: stream}),
          append_string: (s1, s2)=>s1 + s2,
          write_string:
          s=>{
           var start = 0, len = s.length;
           for(;;){
            const
             {read, written} = encoder.encodeInto(s.slice(start), out_buffer);
            len -= read;
            if(! len) return written;
            caml_extract_bytes(written);
            start += read;
           }},
          ta_create: (k, sz)=>new typed_arrays[k](sz),
          ta_normalize:
          a=>
             a instanceof Uint32Array
              ? new Int32Array(a.buffer, a.byteOffset, a.length)
              : a,
          ta_kind: a=>typed_arrays.findIndex(c=>a instanceof c),
          ta_length: a=>a.length,
          ta_get_i32: (a, i)=>a[i],
          ta_fill: (a, v)=>a.fill(v),
          ta_blit: (s, d)=>d.set(s),
          ta_subarray: (a, i, j)=>a.subarray(i, j),
          ta_set: (a, b, i)=>a.set(b, i),
          ta_new: len=>new Uint8Array(len),
          ta_copy: (ta, t, s, e)=>ta.copyWithin(t, s, e),
          ta_bytes:
          a=>
             new
              Uint8Array
              (a.buffer, a.byteOffset, a.length * a.BYTES_PER_ELEMENT),
          ta_blit_from_bytes:
          (s, p1, a, p2, l)=>{
           for(let i = 0; i < l; i++) a[p2 + i] = bytes_get(s, p1 + i);},
          ta_blit_to_bytes:
          (a, p1, s, p2, l)=>{
           for(let i = 0; i < l; i++) bytes_set(s, p2 + i, a[p1 + i]);},
          dv_make: a=>new DataView(a.buffer, a.byteOffset, a.byteLength),
          dv_get_f64: call.bind(DV.getFloat64),
          dv_get_f32: call.bind(DV.getFloat32),
          dv_get_i64: call.bind(DV.getBigInt64),
          dv_get_i32: call.bind(DV.getInt32),
          dv_get_i16: call.bind(DV.getInt16),
          dv_get_ui16: call.bind(DV.getUint16),
          dv_get_i8: call.bind(DV.getInt8),
          dv_get_ui8: call.bind(DV.getUint8),
          dv_set_f64: call.bind(DV.setFloat64),
          dv_set_f32: call.bind(DV.setFloat32),
          dv_set_i64: call.bind(DV.setBigInt64),
          dv_set_i32: call.bind(DV.setInt32),
          dv_set_i16: call.bind(DV.setInt16),
          dv_set_i8: call.bind(DV.setInt8),
          littleEndian: new Uint8Array(new Uint32Array([1]).buffer)[0],
          wrap_callback:
          f=>
             function(...args){
              if(args.length === 0) args = [undefined];
              return caml_callback(f, args.length, args, 1);
             },
          wrap_callback_args:
          f=>function(...args){return caml_callback(f, 1, [args], 0);},
          wrap_callback_strict:
          (arity, f)=>
             function(...args){
              args.length = arity;
              return caml_callback(f, arity, args, 0);
             },
          wrap_callback_unsafe:
          f=>function(...args){return caml_callback(f, args.length, args, 2);},
          wrap_meth_callback:
          f=>
             function(...args){
              args.unshift(this);
              return caml_callback(f, args.length, args, 1);
             },
          wrap_meth_callback_args:
          f=>function(...args){return caml_callback(f, 2, [this, args], 0);},
          wrap_meth_callback_strict:
          (arity, f)=>
             function(...args){
              args.length = arity;
              args.unshift(this);
              return caml_callback(f, args.length, args, 0);
             },
          wrap_meth_callback_unsafe:
          f=>
             function(...args){
              args.unshift(this);
              return caml_callback(f, args.length, args, 2);
             },
          wrap_fun_arguments: f=>function(...args){return f(args);},
          format_float:
          (prec, conversion, pad, x)=>{
           function toFixed(x, dp){
            if(Math.abs(x) < 1.0)
             return x.toFixed(dp);
            else{
             var e = Number.parseInt(x.toString().split("+")[1]);
             if(e > 20){
              e -= 20;
              x /= Math.pow(10, e);
              x += new Array(e + 1).join("0");
              if(dp > 0) x = x + "." + new Array(dp + 1).join("0");
              return x;
             }
             else
              return x.toFixed(dp);
            }
           }
           switch(conversion){
             case 0:
              var s = x.toExponential(prec), i = s.length;
              if(s.charAt(i - 3) === "e")
               s = s.slice(0, i - 1) + "0" + s.slice(i - 1);
              break;
             case 1:
              s = toFixed(x, prec); break;
             case 2:
              prec = prec ? prec : 1;
              s = x.toExponential(prec - 1);
              var j = s.indexOf("e"), exp = + s.slice(j + 1);
              if(exp < - 4 || x >= 1e21 || x.toFixed(0).length > prec){
               var i = j - 1;
               while(s.charAt(i) === "0") i--;
               if(s.charAt(i) === ".") i--;
               s = s.slice(0, i + 1) + s.slice(j);
               i = s.length;
               if(s.charAt(i - 3) === "e")
                s = s.slice(0, i - 1) + "0" + s.slice(i - 1);
               break;
              }
              else{
               var p = prec;
               if(exp < 0){
                p -= exp + 1;
                s = x.toFixed(p);
               }
               else
                while(s = x.toFixed(p), s.length > prec + 1) p--;
               if(p){
                var i = s.length - 1;
                while(s.charAt(i) === "0") i--;
                if(s.charAt(i) === ".") i--;
                s = s.slice(0, i + 1);
               }
              }
              break;
           }
           return pad ? " " + s : s;},
          gettimeofday: ()=>new Date().getTime() / 1000,
          times:
          ()=>{
           if(globalThis.process?.cpuUsage){
            var t = globalThis.process.cpuUsage();
            return caml_alloc_times(t.user / 1e6, t.system / 1e6);
           }
           else{
            var t = performance.now() / 1000;
            return caml_alloc_times(t, t);
           }},
          gmtime:
          t=>{
           var
            d = new Date(t * 1000),
            d_num = d.getTime(),
            januaryfirst =
              new Date(Date.UTC(d.getUTCFullYear(), 0, 1)).getTime(),
            doy = Math.floor((d_num - januaryfirst) / 86400000);
           return caml_alloc_tm
                   (d.getUTCSeconds(),
                    d.getUTCMinutes(),
                    d.getUTCHours(),
                    d.getUTCDate(),
                    d.getUTCMonth(),
                    d.getUTCFullYear() - 1900,
                    d.getUTCDay(),
                    doy,
                    false);},
          localtime:
          t=>{
           var
            d = new Date(t * 1000),
            d_num = d.getTime(),
            januaryfirst = new Date(d.getFullYear(), 0, 1).getTime(),
            doy = Math.floor((d_num - januaryfirst) / 86400000),
            jan = new Date(d.getFullYear(), 0, 1),
            jul = new Date(d.getFullYear(), 6, 1),
            stdTimezoneOffset =
              Math.max(jan.getTimezoneOffset(), jul.getTimezoneOffset());
           return caml_alloc_tm
                   (d.getSeconds(),
                    d.getMinutes(),
                    d.getHours(),
                    d.getDate(),
                    d.getMonth(),
                    d.getFullYear() - 1900,
                    d.getDay(),
                    doy,
                    d.getTimezoneOffset() < stdTimezoneOffset);},
          mktime:
          (year, month, day, h, m, s)=>
             new Date(year, month, day, h, m, s).getTime(),
          random_seed: ()=>crypto.getRandomValues(new Int32Array(12)),
          access:
          (p, flags)=>
             fs.accessSync
              (p,
               access_flags.reduce((f, v, i)=>flags & 1 << i ? f | v : f, 0)),
          open:
          (p, flags, perm)=>
             fs.openSync
              (p,
               open_flags.reduce((f, v, i)=>flags & 1 << i ? f | v : f, 0),
               perm),
          close: fd=>fs.closeSync(fd),
          write:
          (fd, b, o, l, p)=>
             fs
              ? fs.writeSync(fd, b, o, l, p === null ? p : Number(p))
              : (console
                  [fd === 2 ? "error" : "log"]
                 (typeof b === "string"
                   ? b
                   : decoder.decode(b.slice(o, o + l))),
                l),
          read: (fd, b, o, l, p)=>fs.readSync(fd, b, o, l, p),
          fsync: fd=>fs.fsyncSync(fd),
          file_size: fd=>fs.fstatSync(fd, {bigint: true}).size,
          register_channel: register_channel,
          unregister_channel: unregister_channel,
          channel_list: channel_list,
          exit: n=>isNode && globalThis.process.exit(n),
          argv: ()=>isNode ? globalThis.process.argv.slice(1) : ["a.out"],
          on_windows: + on_windows,
          getenv: getenv,
          backtrace_status: ()=>record_backtrace_flag,
          record_backtrace: b=>record_backtrace_flag = b,
          system:
          c=>{
           var
            res =
              require("node:child_process").spawnSync
               (c, {shell: true, stdio: "inherit"});
           if(res.error) throw res.error;
           return res.signal ? 255 : res.status;},
          isatty: fd=>+ require("node:tty").isatty(fd),
          time: ()=>performance.now(),
          getcwd: ()=>isNode ? globalThis.process.cwd() : "/static",
          chdir: x=>globalThis.process.chdir(x),
          mkdir: (p, m)=>fs.mkdirSync(p, m),
          rmdir: p=>fs.rmdirSync(p),
          link: (d, s)=>fs.linkSync(d, s),
          symlink:
          (t, p, kind)=>fs.symlinkSync(t, p, [null, "file", "dir"][kind]),
          readlink: p=>fs.readlinkSync(p),
          unlink: p=>fs.unlinkSync(p),
          read_dir: p=>fs.readdirSync(p),
          opendir: p=>fs.opendirSync(p),
          readdir:
          d=>{var n = d.readSync()?.name; return n === undefined ? null : n;},
          closedir: d=>d.closeSync(),
          stat: (p, l)=>alloc_stat(fs.statSync(p), l),
          lstat: (p, l)=>alloc_stat(fs.lstatSync(p), l),
          fstat: (fd, l)=>alloc_stat(fs.fstatSync(fd), l),
          chmod: (p, perms)=>fs.chmodSync(p, perms),
          fchmod: (p, perms)=>fs.fchmodSync(p, perms),
          file_exists: p=>+ fs.existsSync(p),
          is_directory: p=>+ fs.lstatSync(p).isDirectory(),
          is_file: p=>+ fs.lstatSync(p).isFile(),
          utimes: (p, a, m)=>fs.utimesSync(p, a, m),
          truncate: (p, l)=>fs.truncateSync(p, l),
          ftruncate: (fd, l)=>fs.ftruncateSync(fd, l),
          rename:
          (o, n)=>{
           var n_stat;
           if
            (on_windows && (n_stat = fs.statSync(n, {throwIfNoEntry: false}))
             && fs.statSync(o, {throwIfNoEntry: false})?.isDirectory())
            if(n_stat.isDirectory()){
             if(! n.startsWith(o)) try{fs.rmdirSync(n);}catch{}
            }
            else{
             var
              e =
                new Error(`ENOTDIR: not a directory, rename '${o}' -> '${n}'`);
             throw Object.assign
                    (e,
                     {errno: - 20, code: "ENOTDIR", syscall: "rename", path: n});
            }
           fs.renameSync(o, n);},
          tmpdir: ()=>require("node:os").tmpdir(),
          start_fiber: x=>start_fiber(x),
          suspend_fiber: make_suspending((f, env)=>new Promise(k=>f(k, env))),
          resume_fiber: (k, v)=>k(v),
          weak_new: v=>new WeakRef(v),
          weak_deref:
          w=>{var v = w.deref(); return v === undefined ? null : v;},
          weak_map_new: ()=>new WeakMap(),
          map_new: ()=>new Map(),
          map_get:
          (m, x)=>{var v = m.get(x); return v === undefined ? null : v;},
          map_set: (m, x, v)=>m.set(x, v),
          map_delete: (m, x)=>m.delete(x),
          hash_string: hash_string,
          log: x=>console.log(x)},
       string_ops =
         {test: v=>+ (typeof v === "string"),
          compare: (s1, s2)=>s1 < s2 ? - 1 : + (s1 > s2),
          decodeStringFromUTF8Array: ()=>"",
          encodeStringToUTF8Array: ()=>0,
          fromCharCodeArray: ()=>""},
       imports =
         Object.assign
          ({Math: math,
            bindings: bindings,
            js: js,
            "wasm:js-string": string_ops,
            "wasm:text-decoder": string_ops,
            "wasm:text-encoder": string_ops,
            str: new globalThis.Proxy({}, {get(_, prop){return prop;}}),
            env: {}},
           generated),
       options =
         {builtins: ["js-string", "text-decoder", "text-encoder"],
          importedStringConstants: "str"};
      function loadRelative(src){
       const
        path = require("node:path"),
        f = path.join(path.dirname(require.main.filename), src);
       return require("node:fs/promises").readFile(f);
      }
      const fetchBase = globalThis?.document?.currentScript?.src;
      function fetchRelative(src){
       const url = fetchBase ? new URL(src, fetchBase) : src;
       return fetch(url);
      }
      const loadCode = isNode ? loadRelative : fetchRelative;
      async function instantiateModule(code){
       return isNode
               ? WebAssembly.instantiate(await code, imports, options)
               : WebAssembly.instantiateStreaming(code, imports, options);
      }
      async function instantiateFromDir(){
       imports.OCaml = {};
       const deps = [];
       async function loadModule(module, isRuntime){
        const sync = module[1].constructor !== Array;
        async function instantiate(){
         const code = loadCode(src + "/" + module[0] + ".wasm");
         await Promise.all(sync ? deps : module[1].map(i=>deps[i]));
         const wasmModule = await instantiateModule(code);
         Object.assign
          (isRuntime ? imports.env : imports.OCaml,
           wasmModule.instance.exports);
        }
        const promise = instantiate();
        deps.push(promise);
        return promise;
       }
       async function loadModules(lst){
        for(const module of lst) await loadModule(module);
       }
       await loadModule(link[0], 1);
       if(link.length > 1){
        await loadModule(link[1]);
        const
         workers = new Array(20).fill(link.slice(2).values()).map(loadModules);
        await Promise.all(workers);
       }
       return {instance: {exports: Object.assign(imports.env, imports.OCaml)}};
      }
      const wasmModule = await instantiateFromDir();
      var
       {caml_callback,
         caml_alloc_times,
         caml_alloc_tm,
         caml_alloc_stat,
         caml_start_fiber,
         caml_handle_uncaught_exception,
         caml_buffer,
         caml_extract_bytes,
         bytes_get,
         bytes_set,
         _initialize}
        = wasmModule.instance.exports,
       buffer = caml_buffer?.buffer,
       out_buffer = buffer && new Uint8Array(buffer, 0, buffer.length);
      start_fiber = make_promising(caml_start_fiber);
      var _initialize = make_promising(_initialize);
      if(globalThis.process?.on)
       globalThis.process.on
        ("uncaughtException",
         (err, _origin)=>caml_handle_uncaught_exception(err));
      else if(globalThis.addEventListener)
       globalThis.addEventListener
        ("error",
         event=>event.error && caml_handle_uncaught_exception(event.error));
      await _initialize();})
 (function(globalThis){
    "use strict";
    function caml_js_html_entities(s){
     var entity = /^&#?[0-9a-zA-Z]+;$/;
     if(s.match(entity)){
      var str, temp = document.createElement("p");
      temp.innerHTML = s;
      str = temp.textContent || temp.innerText;
      temp = null;
      return str;
     }
     else
      return null;
    }
    var caml_js_regexps = {amp: /&/g, lt: /</g, quot: /"/g, all: /[&<"]/};
    function caml_js_html_escape(s){
     if(! caml_js_regexps.all.test(s)) return s;
     return s.replace(caml_js_regexps.amp, "&amp;").replace
              (caml_js_regexps.lt, "&lt;").replace
             (caml_js_regexps.quot, "&quot;");
    }
    var
     unix_error =
       ["E2BIG",
        "EACCES",
        "EAGAIN",
        "EBADF",
        "EBUSY",
        "ECHILD",
        "EDEADLK",
        "EDOM",
        "EEXIST",
        "EFAULT",
        "EFBIG",
        "EINTR",
        "EINVAL",
        "EIO",
        "EISDIR",
        "EMFILE",
        "EMLINK",
        "ENAMETOOLONG",
        "ENFILE",
        "ENODEV",
        "ENOENT",
        "ENOEXEC",
        "ENOLCK",
        "ENOMEM",
        "ENOSPC",
        "ENOSYS",
        "ENOTDIR",
        "ENOTEMPTY",
        "ENOTTY",
        "ENXIO",
        "EPERM",
        "EPIPE",
        "ERANGE",
        "EROFS",
        "ESPIPE",
        "ESRCH",
        "EXDEV",
        "EWOULDBLOCK",
        "EINPROGRESS",
        "EALREADY",
        "ENOTSOCK",
        "EDESTADDRREQ",
        "EMSGSIZE",
        "EPROTOTYPE",
        "ENOPROTOOPT",
        "EPROTONOSUPPORT",
        "ESOCKTNOSUPPORT",
        "EOPNOTSUPP",
        "EPFNOSUPPORT",
        "EAFNOSUPPORT",
        "EADDRINUSE",
        "EADDRNOTAVAIL",
        "ENETDOWN",
        "ENETUNREACH",
        "ENETRESET",
        "ECONNABORTED",
        "ECONNRESET",
        "ENOBUFS",
        "EISCONN",
        "ENOTCONN",
        "ESHUTDOWN",
        "ETOOMANYREFS",
        "ETIMEDOUT",
        "ECONNREFUSED",
        "EHOSTDOWN",
        "EHOSTUNREACH",
        "ELOOP",
        "EOVERFLOW"];
    function caml_strerror(errno){
     const util = require("node:util");
     if(errno >= 0){
      const code = unix_error[errno];
      return util.getSystemErrorMap().entries().find(x=>x[1][0] === code)[1]
              [1];
     }
     else
      return util.getSystemErrorMessage(errno);
    }
    return {unix_error: unix_error,
            caml_strerror: caml_strerror,
            caml_js_html_escape: caml_js_html_escape,
            caml_js_html_entities: caml_js_html_entities};
   }
   (globalThis))
({"link":[["runtime-c8715436",0],["prelude-d7e4b000",0],["stdlib-9d9d840a",[]],["ber-a92070b5",[2]],["jsoo_runtime-1e55b178",[2]],["js_of_ocaml-f9e86417",[2,4]],["ocamlcommon-6ec88150",[2]],["astlib-6a2a045c",[2,6]],["ppxlib_ast-6672a571",[2,7]],["ocaml_shadow-0ebf7fe4",[]],["ppxlib_print_diff-2dcabf73",[2]],["ppx_derivers-a78b6a53",[2]],["ppxlib_traverse_builtins-76a3459c",[2]],["sexplib0-026ed491",[2]],["stdppx-1a164a6d",[2,13]],["ppxlib-92cd80e8",[2,7,8,9,10,11,12,13,14]],["ppx_js-19c879e1",[2,6,8,15]],["ppx_js_rewriter-c5d03a14",[16]],["dune__exe__Ber_wasm-2f705596",[2,3,5]],["std_exit-73ee5fad",[2]],["start-fdb66ab7",0]],"generated":(a=>{var
c=a,b=a?.module?.export||a;return{"env":{"caml_ba_kind_of_typed_array":()=>{throw new
Error("caml_ba_kind_of_typed_array not implemented")},"caml_dynlink_add_primitive":()=>{throw new
Error("caml_dynlink_add_primitive not implemented")},"caml_dynlink_close_lib":()=>{throw new
Error("caml_dynlink_close_lib not implemented")},"caml_dynlink_get_current_libs":()=>{throw new
Error("caml_dynlink_get_current_libs not implemented")},"caml_dynlink_lookup_symbol":()=>{throw new
Error("caml_dynlink_lookup_symbol not implemented")},"caml_dynlink_open_lib":()=>{throw new
Error("caml_dynlink_open_lib not implemented")},"caml_exn_with_js_backtrace":()=>{throw new
Error("caml_exn_with_js_backtrace not implemented")},"caml_get_section_table":()=>{throw new
Error("caml_get_section_table not implemented")},"caml_int64_create_lo_mi_hi":()=>{throw new
Error("caml_int64_create_lo_mi_hi not implemented")},"caml_jsoo_flags_effects":()=>{throw new
Error("caml_jsoo_flags_effects not implemented")},"caml_list_mount_point":()=>{throw new
Error("caml_list_mount_point not implemented")},"caml_ml_set_channel_output":()=>{throw new
Error("caml_ml_set_channel_output not implemented")},"caml_ml_set_channel_refill":()=>{throw new
Error("caml_ml_set_channel_refill not implemented")},"caml_realloc_global":()=>{throw new
Error("caml_realloc_global not implemented")},"caml_unmount":()=>{throw new
Error("caml_unmount not implemented")}},"Js_of_ocaml__Js.fragments":{"fun_call_1":(a,b)=>a(b),"get_Array":a=>a.Array,"get_Date":a=>a.Date,"get_Error":a=>a.Error,"get_JSON":a=>a.JSON,"get_Math":a=>a.Math,"get_Object":a=>a.Object,"get_RegExp":a=>a.RegExp,"get_String":a=>a.String,"get_decodeURI":a=>a.decodeURI,"get_decodeURIComponent":a=>a.decodeURIComponent,"get_encodeURI":a=>a.encodeURI,"get_encodeURIComponent":a=>a.encodeURIComponent,"get_escape":a=>a.escape,"get_isNaN":a=>a.isNaN,"get_length":a=>a.length,"get_message":a=>a.message,"get_name":a=>a.name,"get_parseFloat":a=>a.parseFloat,"get_parseInt":a=>a.parseInt,"get_stack":a=>a.stack,"get_unescape":a=>a.unescape,"js_expr_12c48ca8":()=>a,"js_expr_21711c2a":()=>b,"js_expr_26f07992":()=>null,"js_expr_28647a4c":()=>false,"js_expr_34edcf72":()=>true,"js_expr_ba692c1":()=>undefined,"meth_call_0_toString":a=>a.toString(),"meth_call_1_forEach":(a,b)=>a.forEach(b),"meth_call_1_keys":(a,b)=>a.keys(b),"meth_call_1_map":(a,b)=>a.map(b)},"Js_of_ocaml__Dom.fragments":{"call_1":(a,b,c)=>a.call(b,c),"get_CustomEvent":a=>a.CustomEvent,"get_addEventListener":a=>a.addEventListener,"get_length":a=>a.length,"get_nodeType":a=>a.nodeType,"get_srcElement":a=>a.srcElement,"get_target":a=>a.target,"meth_call_0_preventDefault":a=>a.preventDefault(),"meth_call_1_appendChild":(a,b)=>a.appendChild(b),"meth_call_1_concat":(a,b)=>a.concat(b),"meth_call_1_item":(a,b)=>a.item(b),"meth_call_1_removeChild":(a,b)=>a.removeChild(b),"meth_call_2_attachEvent":(a,b,c)=>a.attachEvent(b,c),"meth_call_2_detachEvent":(a,b,c)=>a.detachEvent(b,c),"meth_call_2_insertBefore":(a,b,c)=>a.insertBefore(b,c),"meth_call_2_replaceChild":(a,b,c)=>a.replaceChild(b,c),"meth_call_3_addEventListener":(a,b,c,d)=>a.addEventListener(b,c,d),"meth_call_3_removeEventListener":(a,b,c,d)=>a.removeEventListener(b,c,d),"new_2":(a,b,c)=>new
a(b,c),"obj_0":()=>({}),"obj_1":()=>({}),"set_bubbles":(a,b)=>a.bubbles=b,"set_cancelable":(a,b)=>a.cancelable=b,"set_capture":(a,b)=>a.capture=b,"set_detail":(a,b)=>a.detail=b,"set_once":(a,b)=>a.once=b,"set_passive":(a,b)=>a.passive=b},"Js_of_ocaml__Typed_array.fragments":{"get_ArrayBuffer":a=>a.ArrayBuffer,"get_DataView":a=>a.DataView,"get_Float32Array":a=>a.Float32Array,"get_Float64Array":a=>a.Float64Array,"get_Int16Array":a=>a.Int16Array,"get_Int32Array":a=>a.Int32Array,"get_Int8Array":a=>a.Int8Array,"get_Uint16Array":a=>a.Uint16Array,"get_Uint32Array":a=>a.Uint32Array,"get_Uint8Array":a=>a.Uint8Array,"new_1":(a,b)=>new
a(b)},"Js_of_ocaml__File.fragments":{"get_Blob":a=>a.Blob,"get_Document":a=>a.Document,"get_FileReader":a=>a.FileReader,"get_fileName":a=>a.fileName,"get_name":a=>a.name,"new_2":(a,b,c)=>new
a(b,c)},"Js_of_ocaml__Dom_html.fragments":{"fun_call_1":(a,b)=>a(b),"get_HTMLElement":a=>a.HTMLElement,"get_KeyboardEvent":a=>a.KeyboardEvent,"get_MessageEvent":a=>a.MessageEvent,"get_MouseEvent":a=>a.MouseEvent,"get_MouseScrollEvent":a=>a.MouseScrollEvent,"get_PopStateEvent":a=>a.PopStateEvent,"get_WheelEvent":a=>a.WheelEvent,"get_body":a=>a.body,"get_button":a=>a.button,"get_charCode":a=>a.charCode,"get_clientLeft":a=>a.clientLeft,"get_clientTop":a=>a.clientTop,"get_clientX":a=>a.clientX,"get_clientY":a=>a.clientY,"get_code":a=>a.code,"get_document":a=>a.document,"get_documentElement":a=>a.documentElement,"get_getContext":a=>a.getContext,"get_history":a=>a.history,"get_key":a=>a.key,"get_keyCode":a=>a.keyCode,"get_left":a=>a.left,"get_length":a=>a.length,"get_location":a=>a.location,"get_mozRequestAnimationFrame":a=>a.mozRequestAnimationFrame,"get_msRequestAnimationFrame":a=>a.msRequestAnimationFrame,"get_name":a=>a.name,"get_oRequestAnimationFrame":a=>a.oRequestAnimationFrame,"get_origin":a=>a.origin,"get_pageX":a=>a.pageX,"get_pageY":a=>a.pageY,"get_placeholder":a=>a.placeholder,"get_pushState":a=>a.pushState,"get_relatedTarget":a=>a.relatedTarget,"get_requestAnimationFrame":a=>a.requestAnimationFrame,"get_required":a=>a.required,"get_scrollLeft":a=>a.scrollLeft,"get_scrollTop":a=>a.scrollTop,"get_stopPropagation":a=>a.stopPropagation,"get_tagName":a=>a.tagName,"get_top":a=>a.top,"get_webkitRequestAnimationFrame":a=>a.webkitRequestAnimationFrame,"get_wheelDelta":a=>a.wheelDelta,"get_wheelDeltaX":a=>a.wheelDeltaX,"get_wheelDeltaY":a=>a.wheelDeltaY,"get_which":a=>a.which,"js_expr_4c8b1c6":()=>[].slice,"meth_call_0_getBoundingClientRect":a=>a.getBoundingClientRect(),"meth_call_0_getTime":a=>a.getTime(),"meth_call_0_stopPropagation":a=>a.stopPropagation(),"meth_call_0_toLowerCase":a=>a.toLowerCase(),"meth_call_1_call":(a,b)=>a.call(b),"meth_call_1_charCodeAt":(a,b)=>a.charCodeAt(b),"meth_call_1_clearTimeout":(a,b)=>a.clearTimeout(b),"meth_call_1_createElement":(a,b)=>a.createElement(b),"meth_call_1_getElementById":(a,b)=>a.getElementById(b),"meth_call_1_join":(a,b)=>a.join(b),"meth_call_1_push":(a,b)=>a.push(b),"meth_call_2_push":(a,b,c)=>a.push(b,c),"meth_call_2_setTimeout":(a,b,c)=>a.setTimeout(b,c),"meth_call_3_push":(a,b,c,d)=>a.push(b,c,d),"new_0":a=>new
a(),"set_cancelBubble":(a,b)=>a.cancelBubble=b,"set_name":(a,b)=>a.name=b,"set_type":(a,b)=>a.type=b},"Js_of_ocaml__Form.fragments":{"get_FormData":a=>a.FormData,"get_checked":a=>a.checked,"get_disabled":a=>a.disabled,"get_elements":a=>a.elements,"get_files":a=>a.files,"get_length":a=>a.length,"get_multiple":a=>a.multiple,"get_name":a=>a.name,"get_options":a=>a.options,"get_selected":a=>a.selected,"get_type":a=>a.type,"get_value":a=>a.value,"meth_call_0_toLowerCase":a=>a.toLowerCase(),"meth_call_1_item":(a,b)=>a.item(b),"meth_call_2_append":(a,b,c)=>a.append(b,c),"new_0":a=>new
a()},"Js_of_ocaml__Worker.fragments":{"get_Worker":a=>a.Worker,"get_data":a=>a.data,"get_importScripts":a=>a.importScripts,"get_onmessage":a=>a.onmessage,"get_postMessage":a=>a.postMessage,"meth_call_1_postMessage":(a,b)=>a.postMessage(b),"new_1":(a,b)=>new
a(b),"set_onmessage":(a,b)=>a.onmessage=b},"Js_of_ocaml__WebSockets.fragments":{"get_WebSocket":a=>a.WebSocket},"Js_of_ocaml__WebGL.fragments":{"meth_call_1_getContext":(a,b)=>a.getContext(b),"meth_call_2_getContext":(a,b,c)=>a.getContext(b,c),"obj_2":(a,b,c,d,e,f,g,h)=>({alpha:a,depth:b,stencil:c,antialias:d,premultipliedAlpha:e,preserveDrawingBuffer:f,preferLowPowerToHighPerformance:g,failIfMajorPerformanceCaveat:h})},"Js_of_ocaml__Regexp.fragments":{"get_ignoreCase":a=>a.ignoreCase,"get_index":a=>a.index,"get_length":a=>a.length,"get_multiline":a=>a.multiline,"get_source":a=>a.source,"meth_call_1_exec":(a,b)=>a.exec(b),"meth_call_1_split":(a,b)=>a.split(b),"meth_call_2_replace":(a,b,c)=>a.replace(b,c),"meth_call_2_split":(a,b,c)=>a.split(b,c),"new_2":(a,b,c)=>new
a(b,c),"set_lastIndex":(a,b)=>a.lastIndex=b},"Js_of_ocaml__Url.fragments":{"get_hash":a=>a.hash,"get_hostname":a=>a.hostname,"get_href":a=>a.href,"get_length":a=>a.length,"get_location":a=>a.location,"get_pathname":a=>a.pathname,"get_port":a=>a.port,"get_protocol":a=>a.protocol,"get_search":a=>a.search,"meth_call_0_toLowerCase":a=>a.toLowerCase(),"meth_call_1_charAt":(a,b)=>a.charAt(b),"meth_call_1_exec":(a,b)=>a.exec(b),"meth_call_1_indexOf":(a,b)=>a.indexOf(b),"meth_call_1_slice":(a,b)=>a.slice(b),"meth_call_1_split":(a,b)=>a.split(b),"meth_call_2_replace":(a,b,c)=>a.replace(b,c),"meth_call_2_slice":(a,b,c)=>a.slice(b,c),"new_1":(a,b)=>new
a(b),"new_2":(a,b,c)=>new
a(b,c),"obj_3":(a,b,c,d,e,f,g,h,i,j,k,l)=>({href:a,protocol:b,host:c,hostname:d,port:e,pathname:f,search:g,hash:h,origin:i,reload:j,replace:k,assign:l}),"set_hash":(a,b)=>a.hash=b,"set_href":(a,b)=>a.href=b,"set_lastIndex":(a,b)=>a.lastIndex=b},"Js_of_ocaml__ResizeObserver.fragments":{"get_ResizeObserver":a=>a.ResizeObserver,"meth_call_1_observe":(a,b)=>a.observe(b),"meth_call_2_observe":(a,b,c)=>a.observe(b,c),"new_1":(a,b)=>new
a(b),"obj_4":()=>({}),"obj_5":()=>({}),"set_box":(a,b)=>a.box=b},"Js_of_ocaml__PerformanceObserver.fragments":{"get_PerformanceObserver":a=>a.PerformanceObserver,"meth_call_1_observe":(a,b)=>a.observe(b),"new_1":(a,b)=>new
a(b),"obj_6":()=>({}),"set_entryTypes":(a,b)=>a.entryTypes=b},"Js_of_ocaml__MutationObserver.fragments":{"get_MutationObserver":a=>a.MutationObserver,"meth_call_2_observe":(a,b,c)=>a.observe(b,c),"new_1":(a,b)=>new
a(b),"obj_7":()=>({}),"obj_8":()=>({}),"set_attributeFilter":(a,b)=>a.attributeFilter=b,"set_attributeOldValue":(a,b)=>a.attributeOldValue=b,"set_attributes":(a,b)=>a.attributes=b,"set_characterData":(a,b)=>a.characterData=b,"set_characterDataOldValue":(a,b)=>a.characterDataOldValue=b,"set_childList":(a,b)=>a.childList=b,"set_subtree":(a,b)=>a.subtree=b},"Js_of_ocaml__Jstable.fragments":{"get_Object":a=>a.Object,"get_length":a=>a.length,"meth_call_1_concat":(a,b)=>a.concat(b),"meth_call_1_keys":(a,b)=>a.keys(b),"meth_call_2_substring":(a,b,c)=>a.substring(b,c),"new_0":a=>new
a()},"Js_of_ocaml__Json.fragments":{"get_JSON":a=>a.JSON,"get_constructor":a=>a.constructor,"get_hi":a=>a.hi,"get_length":a=>a.length,"get_lo":a=>a.lo,"get_mi":a=>a.mi,"meth_call_1_stringify":(a,b)=>a.stringify(b),"meth_call_2_parse":(a,b,c)=>a.parse(b,c),"meth_call_2_stringify":(a,b,c)=>a.stringify(b,c)},"Js_of_ocaml__CSS.fragments":{"meth_call_1_test":(a,b)=>a.test(b),"new_1":(a,b)=>new
a(b)},"Js_of_ocaml__Dom_svg.fragments":{"get_SVGElement":a=>a.SVGElement,"get_document":a=>a.document,"get_tagName":a=>a.tagName,"meth_call_0_toLowerCase":a=>a.toLowerCase(),"meth_call_1_getElementById":(a,b)=>a.getElementById(b),"meth_call_2_createElementNS":(a,b,c)=>a.createElementNS(b,c)},"Js_of_ocaml__EventSource.fragments":{"get_EventSource":a=>a.EventSource,"obj_9":()=>({}),"set_withCredentials":(a,b)=>a.withCredentials=b},"Js_of_ocaml__Geolocation.fragments":{"get_geolocation":a=>a.geolocation,"get_navigator":a=>a.navigator,"obj_10":()=>({})},"Js_of_ocaml__IntersectionObserver.fragments":{"get_IntersectionObserver":a=>a.IntersectionObserver,"obj_11":()=>({})},"Js_of_ocaml__Intl.fragments":{"get_Collator":a=>a.Collator,"get_DateTimeFormat":a=>a.DateTimeFormat,"get_Intl":a=>a.Intl,"get_NumberFormat":a=>a.NumberFormat,"get_PluralRules":a=>a.PluralRules,"obj_12":a=>({localeMatcher:a}),"obj_13":(a,b,c,d,e,f)=>({localeMatcher:a,usage:b,sensitivity:c,ignorePunctuation:d,numeric:e,caseFirst:f}),"obj_14":(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t)=>({dateStyle:a,timeStyle:b,calendar:c,dayPeriod:d,numberingSystem:e,localeMatcher:f,timeZone:g,hour12:h,hourCycle:i,formatMatcher:j,weekday:k,era:l,year:m,month:n,day:o,hour:p,minute:q,second:r,fractionalSecondDigits:s,timeZoneName:t}),"obj_15":(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u)=>({compactDisplay:a,currency:b,currencyDisplay:c,currencySign:d,localeMatcher:e,notation:f,numberingSystem:g,signDisplay:h,style:i,unit:j,unitDisplay:k,useGrouping:l,roundingMode:m,roundingPriority:n,roundingIncrement:o,trailingZeroDisplay:p,minimumIntegerDigits:q,minimumFractionDigits:r,maximumFractionDigits:s,minimumSignificantDigits:t,maximumSignificantDigits:u}),"obj_16":(a,b)=>({localeMatcher:a,type:b})},"Dune__exe__Ber_wasm.fragments":{"obj_0":a=>({typecheck:a}),"obj_1":(a,b,c,d,e)=>({startLine:a,startCol:b,endLine:c,endCol:d,label:e}),"obj_2":(a,b,c,d,e,f,g)=>({kind:a,heading:b,got:c,expected:d,marksGot:e,marksExpected:f,occursTy:g}),"obj_3":(a,b,c,d,e,f,g)=>({kind:a,heading:b,got:c,expected:d,marksGot:e,marksExpected:f,occursTy:g}),"obj_4":(a,b,c,d)=>({ok:a,output:b,spans:c,detail:d}),"obj_5":(a,b)=>({start:a,len:b})}}})(globalThis),"src":"ber_wasm.bc.wasm.assets"});
