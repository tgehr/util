module util.optparse;
import std.algorithm: startsWith;
import std.stdio: stderr;
import std.string: indexOf;

private struct OptHandler {
	int value; // 0=no value, 1=has value, -1=may have value (always uses handle1)
	union {
		int delegate() handle0;
		int delegate(string) handle1;
	}
}

private struct BoolHandler {
	string opt;
	int delegate(bool) handle;
	int hTrue0() {
		return handle(true);
	}
	int hTrue1(string v) {
		if(v is null || v == "true") {
			return handle(true);
		}
		if(v == "false") {
			return handle(false);
		}
		stderr.writef("error: --%s expects true or false\n", opt);
		return 1;
	}
	int hFalse0() {
		return handle(false);
	}
}

struct OptParser {
	OptHandler[string] longOpts;
	OptHandler[char] shortOpts;

	private void addHandler(char opt, OptHandler h) {
		assert(opt !in shortOpts);
		shortOpts[opt] = h;
	}

	private void addHandler(string opt, OptHandler h) {
		assert(opt !in longOpts);
		longOpts[opt] = h;
	}

	private static string firstLong(opts...)() {
		static foreach(opt; opts) {
			static if(isLong!(opt)()) return opt;
		}
		return null;
	}

	private static bool isLong(string opt)() {
		return true;
	}

	private static bool isLong(char opt)() {
		return false;
	}

	OptParser add(opts...)(int delegate() handle) {
		static foreach(opt; opts) {
			addHandler(opt, OptHandler(value: 0, handle0: handle));
		}
		return this;
	}

	OptParser add(opts...)(int delegate(string) handle) {
		static foreach(opt; opts) {
			addHandler(opt, OptHandler(value: 1, handle1: handle));
		}
		return this;
	}

	OptParser addOptional(opts...)(int delegate(string) handle) {
		static foreach(opt; opts) {
			addHandler(opt, OptHandler(value: -1, handle1: handle));
		}
		return this;
	}

	OptParser add(opts...)(int delegate(bool) handle) {
		auto h = new BoolHandler(firstLong!(opts)(), handle);
		static foreach(opt; opts) {
			static if(isLong!(opt)()) {
				addOptional!(opt)(&h.hTrue1);
				add!("no-" ~ opt)(&h.hFalse0);
			} else {
				add!(opt)(&h.hTrue0);
			}
		}
		return this;
	}

	int parse(ref string[] args) {
		size_t keep = 1;
		size_t i = 1;

		while(i < args.length) {
			string arg = args[i++];
			if(!arg.startsWith("-")) {
				args[keep++] = arg;
				continue;
			}
			if(arg.startsWith("--")) {
				if(arg == "--") {
					for (; i < args.length; i++) {
						args[keep++] = args[i];
					}
					break;
				}
				// long option
				auto pos = arg.indexOf('=');
				string value = null;
				if(pos >= 0) {
					value = arg[pos+1..$];
				} else {
					pos = arg.length;
				}
				arg = arg[2..pos];
				auto opt = arg in longOpts;
				if(!opt) {
					stderr.writef("error: unknown option --%s\n", arg);
					return 1;
				}
				int r;
				if(opt.value == 0) {
					if(value !is null) {
						stderr.writef("error: --%s takes no value\n", arg);
						return 1;
					}
					r = opt.handle0();
				}else {
					if(opt.value > 0 && value is null) {
						if(i == args.length) {
							stderr.writef("error: --%s expects a value\n", arg);
							return 1;
						}
						value = args[i++];
					}
					r = opt.handle1(value);
				}
				if(r) return r;
				continue;
			}
			size_t j = 1;
			while(j < arg.length) {
				char c = arg[j++];
				auto opt = c in shortOpts;
				if(!opt) {
					stderr.writef("error: unknown option -%c\n", c);
					return 1;
				}
				if(opt.value != 0) {
					if(j == arg.length && opt.value > 0) {
						if(i == args.length) {
							stderr.writef("error: -%c expects a value\n", c);
							return 1;
						}
						arg = args[i++];
					} else {
						arg = arg[j..$];
					}
					int r = opt.handle1(arg);
					if(r) return r;
					break;
				}
				int r = opt.handle0();
				if(r) return r;
			}
		}
		args.length = keep;
		return 0;
	}
}
