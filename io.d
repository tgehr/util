module util.io;

version(WASM){
	struct StdOut{
	static:
		void write(T...)(auto ref T args){}
		void writeln(T...)(auto ref T args){}
		void writefln(T...)(auto ref T args){}
		void flush(){}
	};
	StdOut stdout;
	bool isATTy(StdOut){ return false; }
	static struct StdErr{
	static:
		void write(T...)(auto ref T args){}
		void writeln(T...)(auto ref T args){}
		void writefln(T...)(auto ref T args){}
		static void flush(){}
	}
	StdErr stderr;
	bool isATTy(StdErr){ return false; }
	struct File{
		string path;
		string readln(){ return ""; }
		string[] byChunk(int n){ return []; }
	}
	void writeln(T...)(auto ref T args){
		stdout.writeln(forward!args);
	}
	void writefln(T...)(auto ref T args){
		stdout.writefln(forward!args);
	}
	static struct file{
	static:
		@property string thisExePath(){ return "."; }
		bool exists(string name){ return true; }
	}
}else{
	public import std.stdio;
	public import file=std.file;
}
import core.lifetime:forward;

