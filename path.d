module util.path;

version(WASM){
	string buildPath(string[] args...){
		import std.string;
		return args.join("/");
	}
	string dirName(string arg){
		while(arg.length&&arg[$-1]=='/')
			arg=arg[0..$-1];
		auto i=arg.length;
		if(!i) return "/";
		for(;i-->0;)
			if(arg[i]=='/')
				return arg[0..i];
		return "/";
	}
	string extension(string arg){
		auto i=arg.length;
		if(!i) return "";
		i--;
		for(;i-->0;)
			if(arg[i]=='/')
				return extension(arg[i+1..$]);
		i=arg.length-1;
		for(;i-->0;)
			if(arg[i]=='.')
				return arg[i+1..$];
		return "";
	}
	string setExtension(string arg,string ext){
		auto i=arg.length;
		if(!i) return "";
		i--;
		for(;i-->0;)
			if(arg[i]=='/')
				return arg[0..i+1]~setExtension(arg[i+1..$],ext);
		i=arg.length-1;
		for(;i-->0;)
			if(arg[i]=='.')
				return arg[0..i+1]~ext;
		return "";		
	}
}else public import std.path;
