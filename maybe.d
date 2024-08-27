module util.maybe;

struct Maybe(T){
	private T payload;
	private bool _exists;
	bool opCast(T:bool)(){ return _exists; }
	private this(T payload){
		this.payload=payload;
		_exists=true;
	}
	ref T get()in{
		assert(!!this);
	}do{
		return payload;
	}
	void opAssign(Maybe!T rhs){
		this.payload=rhs.payload;
		this._exists=rhs._exists;
	}
	void opAssign(T rhs){
		this.payload=rhs;
		this._exists=true;
	}
	void clear(){ this=typeof(this).init; }
	string toString()(){
		import std.conv:text;
		if(_exists) return text("just(",payload,")");
		return "none!"~T.stringof;
	}
}

Maybe!T none(T)(){ return Maybe!T(); }
Maybe!T just(T)(T arg){ return Maybe!T(arg); }


template fold(alias yes,alias no){
	auto fold(T)(auto ref Maybe!T arg){
		if(arg._exists) return yes(arg.payload);
		else return no();
	}
}

template map(alias f){
	auto map(T)(auto ref Maybe!T arg){
		return arg.fold!(x=>just(f(x)),()=>none!(typeof(f(arg.payload))));
	}
}

Maybe!T join(T)(Maybe!(Maybe!T) arg){
	if(arg._exists) return arg.payload;
	return none!T;
}

template bind(alias f){
	auto bind(T)(auto ref Maybe!T arg){
		return arg.map!f.join;
	}
}
