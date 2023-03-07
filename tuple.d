module util.tuple;

import std.format:formattedWrite;
import std.conv:text;
import util.hashtable:FNV,fnvb;
import core.lifetime:forward;
import util:opCmp;

struct Tuple(T...){
	T expand;
	alias expand this;
	private static hash_t getHash(T)(ref T x,hash_t b){
		static if(is(T==class)) return FNV(x?x.toHash():0,b);
		else static if(is(T==struct)) return FNV(x.toHash(),b);
		else static if(is(T==string)||is(T==int)) return FNV(typeid(T).getHash(&x),b);
		else static if(is(T==S[],S)||is(T==S[n],S,size_t n)){
			auto r=b;
			foreach(ref y;x) r=getHash(y,r);
			return r;
		}else static if(is(T==U[V],U,V)){
			hash_t r=0;
			foreach(k,v;x) r+=getHash(k,getHash(v,0));
			return FNV(r,b);
		}else static if(is(typeof(cast(hash_t)x))){
			return FNV(cast(hash_t)x,b);
		}else static assert(0,T.stringof);
	}
	hash_t toHash()(){
		auto r=fnvb;
		foreach(i,ref x;expand) r=getHash(x,r);
		return r;
	}
	string toString()(){ return text(this); }
	void toString()(void delegate(scope const(char)[]) sink){
		sink("(");
		foreach(i;0..this.length){
			formattedWrite!"%s"(sink,this[i]);
			static if(expand.length==1||i+1<expand.length) sink(",");
		}
		sink(")");
	}
	int opCmp(T)(auto ref T rhs){
		static foreach(i;0..this.length)
			if(auto r=this[i].opCmp(rhs[i]))
				return r;
		return 0;
	}
}
auto tuple(T...)(auto ref T t){ return Tuple!T(forward!t); }
