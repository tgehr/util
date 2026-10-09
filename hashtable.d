// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0
module util.hashtable;

static if(size_t.sizeof==4) enum fnvp = 16777619U, fnvb = 2166136261U;
else static if(size_t.sizeof==8) enum fnvp = 1099511628211LU, fnvb = 14695981039346656037LU;

size_t FNV(size_t data, size_t start=fnvb){
	return (start^data)*fnvp;
}
size_t mixHash(size_t h){ // murmur3 finalizer, avoids collisions from summing up FNV hashes
	static if(size_t.sizeof==8){
		h^=h>>>33; h*=0xff51afd7ed558ccdLU;
		h^=h>>>33; h*=0xc4ceb3fe1a85ec53LU;
		h^=h>>>33;
	}else{
		h^=h>>>16; h*=0x85ebca6bU;
		h^=h>>>13; h*=0xc2b2ae35U;
		h^=h>>>16;
	}
	return h;
}

import util.tuple, util.maybe, std.typetuple;
import std.functional, std.algorithm;
import std.conv, std.array;
import core.lifetime: copyEmplace, moveEmplace;

//import util;

enum hasMoveConstructors = __traits(compiles,(){
	static struct Probe{
		int x;
		this(Probe p){ this.x=p.x; }
		this(ref inout(Probe) p)inout{ this.x=p.x; }
		@disable this(this);
	}
});

enum Storage{ compact, stable }

enum hasCheapHash(T)=isScalarType!T;

struct HashMap(K_, V_, alias eq_ , alias h_, Storage storage_=Storage.compact, bool storeHash_=!hasCheapHash!K_){
	alias K=K_;
	alias V=V_;
	alias binaryFun!eq_ eq;
	alias unaryFun!h_ h;
	enum stable = storage_==Storage.stable;
	enum storeHash = storeHash_;
	static struct E{ // TODO: why can't the two fields be swapped?
		V v;
		K k;
		static if(storeHash) size_t hash; // h(k), set on insertion
		static if(!is(V==void[0])) this(V v, K k){ this.v=v; this.k=k; }
		else this(K k){ this.k=k; }
		static if(hasMoveConstructors)
			this(E e){ static if(!is(V==void[0])) this.v=move(e.v); static if(!is(K==void[0])) this.k=move(e.k); static if(storeHash) this.hash=e.hash; }
		this(ref inout(E) e)inout{ this.v=e.v; this.k=e.k; static if(storeHash) this.hash=e.hash; }
		@disable this(this);
	}

	private class State{
		static if(stable){
			// Chunk sizes double (4, 8, 16, ...), so that small tables stay small:
			// chunk c holds entry positions [chunkStart(c), chunkStart(c+1)).
			enum firstChunkShift=2;
			static size_t chunkStart(size_t c){ return ((size_t(1)<<c)-1)<<firstChunkShift; }
			static size_t chunkLength(size_t c){ return size_t(1)<<(c+firstChunkShift); }
			static void locate(size_t p,out size_t c,out size_t o){
				import core.bitop:bsr;
				c=bsr((p>>firstChunkShift)+1);
				o=p-chunkStart(c);
			}
			E[][] chunks;     // chunked entry storage
			ubyte[][] tombs;  // tombs[i][j] != 0 iff chunks[i][j] is removed
		}else{
			E[] ealloc;       // capacity buffer for entries
			ubyte[] tombstone; // tombstone[i] != 0 iff ealloc[i] is removed
		}
		size_t eused;     // number of entry slots used (live + tombstones)
		uint[] index;     // entry positions, EMPTY/DELETED are sentinels
		size_t length;    // number of live entries
		size_t deletedSlots;
		static if(!stable) size_t tombstones;

		private enum uint EMPTY=uint.max, DELETED=uint.max-1;
		enum initialIndexSize = 16;

		void initialize(){
			index=new uint[](initialIndexSize);
			index[]=EMPTY;
		}

		private size_t mask(){ return index.length-1; }
		static assert((initialIndexSize&(initialIndexSize-1))==0);

		static if(stable){
			ref E entryAt(size_t p){ size_t c,o; locate(p,c,o); return chunks[c][o]; }
			ref ubyte tombAt(size_t p){ size_t c,o; locate(p,c,o); return tombs[c][o]; }
			size_t appendSlot(){ // returns position of a fresh entry slot
				if(eused==chunkStart(chunks.length)){
					auto n=chunkLength(chunks.length);
					chunks~=new E[](n);
					tombs~=new ubyte[](n);
				}
				return eused++;
			}
		}else{
			ref E entryAt(size_t p){ return ealloc[p]; }
			ref ubyte tombAt(size_t p){ return tombstone[p]; }
			void growEntries(){
				auto nb=new E[](ealloc.length?2*ealloc.length:8);
				foreach(i;0..eused) moveEmplace(ealloc[i],nb[i]);
				ealloc=nb;
				auto nt=new ubyte[](ealloc.length);
				nt[0..eused]=tombstone[0..eused];
				tombstone=nt;
			}
			size_t appendSlot(){ // returns position of a fresh entry slot
				if(eused==ealloc.length) growEntries();
				return eused++;
			}
			void compactEntries(){ // drops tombstones, preserving order
				size_t w=0;
				foreach(r;0..eused)
					if(!tombstone[r]){
						if(w!=r) moveEmplace(ealloc[r],ealloc[w]);
						w++;
					}
				eused=w;
				tombstones=0;
				tombstone[0..eused]=0;
				rehash(index.length);
			}
		}

		// locates k (found=true, entryPos set) or the slot it should occupy
		bool probe(K k,out size_t slot,out size_t entryPos){
			return probe(k,h(k),slot,entryPos);
		}
		// same, with hk==h(k) precomputed by the caller
		bool probe(K k,size_t hk,out size_t slot,out size_t entryPos){
			auto i=slotOf(hk)&mask, firstDeleted=size_t.max;
			while(true){
				auto ix=index[i];
				if(ix==EMPTY){
					slot=firstDeleted!=size_t.max?firstDeleted:i;
					return false;
				}
				if(ix==DELETED){ if(firstDeleted==size_t.max) firstDeleted=i; }
				else if(hashMayMatch(ix,hk)&&eq(k,entryAt(ix).k)){ slot=i; entryPos=ix; return true; }
				i=(i+1)&mask;
			}
		}

		// Many hashes have weak low bits (e.g., the default toHash of class objects is their
		// address), so index slots are derived from the middle bits of a Fibonacci hash,
		// which depend on all lower bits of the hash. Integer keys are typically hashed
		// by identity and often dense, where taking the low bits directly is best.
		enum mixSlots=!isIntegral!K&&!isSomeChar!K&&!is(K==bool);
		static size_t slotOf(size_t hk){
			static if(!mixSlots) return hk;
			else static if(size_t.sizeof==8) return (hk*0x9e3779b97f4a7c15LU)>>>32; // (index sizes are < 2^32)
			else return mixHash(hk); // (a 32-bit Fibonacci hash would leave too few usable bits)
		}
		// h of the key of the (live) entry at position p
		size_t hashAt(size_t p){
			static if(storeHash) return entryAt(p).hash;
			else return h(entryAt(p).k);
		}
		// false if the key at position p certainly does not have hash hk
		bool hashMayMatch(size_t p,size_t hk){
			static if(storeHash) return entryAt(p).hash==hk;
			else return true;
		}

		void rehash(size_t newSize){
			auto ni=new uint[](newSize);
			ni[]=EMPTY;
			auto nmask=newSize-1;
			foreach(pos;0..eused){
				if(tombAt(pos)) continue;
				auto i=slotOf(hashAt(pos))&nmask;
				while(ni[i]!=EMPTY) i=(i+1)&nmask;
				ni[i]=cast(uint)pos;
			}
			index=ni;
			deletedSlots=0;
		}

		// makes room for one more entry; returns whether the index was rebuilt
		// (which invalidates slots obtained from earlier probes)
		bool ensureCapacity(){
			if(10*(length+deletedSlots+1)>7*index.length){
				static if(!stable){
					if(tombstones*2>length+1){
						compactEntries();
						return true;
					}
				}
				rehash(index.length*2);
				return true;
			}
			return false;
		}

		ref V insert(E x, out bool isNew){
			if(!index.length) initialize();
			ensureCapacity();
			immutable hk=h(x.k);
			static if(storeHash) x.hash=hk; // (x may overwrite an existing entry)
			size_t s,p;
			if(probe(x.k,hk,s,p)){
				copyEmplace(x, entryAt(p));
				isNew=false;
				return entryAt(p).v;
			}
			isNew=true;
			return insertAt(move(x),hk,s);
		}

		// inserts x, whose key must be absent and have hash hk, at index slot s, which
		// must come from a probe for x.k made after the last index rebuild (see ensureCapacity)
		ref V insertAt(E x, size_t hk, size_t s){
			if(index[s]==DELETED) deletedSlots--;
			assert(eused<DELETED); // indices must fit
			auto pos=appendSlot();
			index[s]=cast(uint)pos;
			copyEmplace(x, entryAt(pos));
			static if(storeHash) entryAt(pos).hash=hk;
			tombAt(pos)=0;
			length++;
			return entryAt(pos).v;
		}

		// like insertAt, but makes room first; s is used only if haveSlot and the
		// table is not rebuilt in the meantime (otherwise, x.k is probed again)
		ref V insertAbsent(E x, size_t hk, size_t s, bool haveSlot){
			if(!index.length){ initialize(); haveSlot=false; }
			if(ensureCapacity()) haveSlot=false;
			size_t p;
			if(!haveSlot) probe(x.k,hk,s,p); // (x.k is absent, this only locates a free slot)
			return insertAt(move(x),hk,s);
		}

		// removes the entry at position p, which was found at index slot s
		void removeAt(size_t s,size_t p){
			index[s]=DELETED;
			deletedSlots++;
			tombAt(p)=1;
			static if(!stable) tombstones++;
			entryAt(p).v=V.init; // release references
			entryAt(p).k=K.init;
			length--;
		}
	}

	private State state;
	private State ensureState(){ if(!state) state=new State; return state; }

	@property size_t length()const{ return state?state.length:0; }

	bool opBinaryRight(string op: "in")(K k){
		size_t s,p;
		return state&&state.probe(k,s,p);
	}

	V get(K k, lazy V alt){
		size_t s,p;
		if(state&&state.probe(k,s,p)) return state.entryAt(p).v;
		return alt;
	}

	static if(stable)
	V* getPtr(K k){ // remains valid across insertions/removals of other entries
		size_t s,p;
		if(state&&state.probe(k,s,p)) return &state.entryAt(p).v;
		return null;
	}

	// like getPtr, but the result must be used immediately (it is not
	// guaranteed to survive the next mutation of the table)
	private V* findPtr(K k){
		size_t s,p;
		if(state&&state.probe(k,s,p)) return &state.entryAt(p).v;
		return null;
	}

	static if(stable){
		ref V opIndex(K k){ // unlike the built-in AA, reading a missing key is an error
			size_t s,p;
			if(state&&state.probe(k,s,p)) return state.entryAt(p).v;
			static if(is(typeof(text(k)))) assert(0, text("key not found: ",k));
			else assert(0, "key not found");
		}

		ref V require(K k, lazy V alt){
			size_t s,p;
			if(state&&state.probe(k,s,p)) return state.entryAt(p).v;
			bool isNew;
			static if(is(V==void[0])) return ensureState().insert(E(k),isNew);
			else return ensureState().insert(E(alt,k),isNew);
		}
	}else{
		V opIndex(K k){ // by value; reading a missing key is an error
			size_t s,p;
			if(state&&state.probe(k,s,p)) return state.entryAt(p).v;
			static if(is(typeof(text(k)))) assert(0, text("key not found: ",k));
			else assert(0, "key not found");
		}
	}

	bool remove(K k){
		if(!state) return false;
		size_t s,p;
		if(!state.probe(k,s,p)) return false;
		state.removeAt(s,p);
		return true;
	}

	static if(stable){
		ref V opIndexAssign(V v, K k){
			bool isNew;
			static if(is(V==void[0])) return ensureState().insert(E(k),isNew);
			else return ensureState().insert(E(v,k),isNew);
		}
	}else{
		void opIndexAssign(V v, K k){
			bool isNew;
			static if(is(V==void[0])) ensureState().insert(E(k),isNew);
			else ensureState().insert(E(v,k),isNew);
		}
	}
	void opIndexOpAssign(string op,W)(W w, K k){
		immutable hk=h(k);
		size_t s,p;
		immutable probed=state&&state.index.length;
		if(probed&&state.probe(k,hk,s,p)){
			mixin(`state.entryAt(p).v `~op~`= w;`);
			return;
		}
		V v; mixin(`v` ~op~`= w;`);
		static if(is(V==void[0])) ensureState().insertAbsent(E(k),hk,s,probed);
		else ensureState().insertAbsent(E(v,k),hk,s,probed);
	}

	int opApply(scope int delegate(ref V) dg){
		if(!state) return 0;
		immutable n=state.eused; // do not iterate entries inserted by the loop body
		foreach(i;0..n) if(!state.tombAt(i)) if(auto r=dg(state.entryAt(i).v)) return r;
		return 0;
	}
	int opApply(scope int delegate(ref K,ref V) dg){
		if(!state) return 0;
		immutable n=state.eused;
		foreach(i;0..n) if(!state.tombAt(i)) if(auto r=dg(state.entryAt(i).k, state.entryAt(i).v)) return r;
		return 0;
	}

	static if(stable){
		private static struct EntryRange{
			private E[][] chunks;
			private ubyte[][] tombs;
			private size_t pos, n;
			private bool tombAt(size_t p){ size_t c,o; State.locate(p,c,o); return !!tombs[c][o]; }
			private void skip(){ while(pos<n&&tombAt(pos)) pos++; }
			private this(E[][] chunks,ubyte[][] tombs,size_t n){ this.chunks=chunks; this.tombs=tombs; this.n=n; skip(); }
			@property bool empty(){ return pos>=n; }
			@property ref E front(){ size_t c,o; State.locate(pos,c,o); return chunks[c][o]; }
			void popFront(){ pos++; skip(); }
		}
		@property byKeyValue(){ return state?EntryRange(state.chunks,state.tombs,state.eused):EntryRange.init; }
	}else{
		private static struct EntryRange{
			private E[] entries;
			private ubyte[] tombstone;
			private size_t pos;
			private void skip(){ while(pos<entries.length&&tombstone[pos]) pos++; }
			private this(E[] entries,ubyte[] tombstone){ this.entries=entries; this.tombstone=tombstone; skip(); }
			@property bool empty(){ return pos>=entries.length; }
			@property ref E front(){ return entries[pos]; }
			void popFront(){ pos++; skip(); }
		}
		@property byKeyValue(){ return state?EntryRange(state.ealloc[0..state.eused],state.tombstone[0..state.eused]):EntryRange.init; }
	}
	@property keys(){ return byKeyValue.map!((ref x)=>x.k); }
	@property values(){ return byKeyValue.map!(function ref(ref x)=>x.v); }
	@property byKey(){ return keys; }
	@property byValue(){ return values; }

	bool opEquals()(ref HashMap rhs){
		// equal lengths and all keys of this in rhs imply equal key sets
		if(length!=rhs.length) return false;
		if(!length) return true;
		foreach(i;0..state.eused){
			if(state.tombAt(i)) continue;
			size_t s,p;
			if(!rhs.state.probe(state.entryAt(i).k,state.hashAt(i),s,p)) return false;
			if(rhs.state.entryAt(p).v!=state.entryAt(i).v) return false;
		}
		return true;
	}
	hash_t toHash()(){
		if(!state) return 0;
		hash_t r=0;
		foreach(i;0..state.eused) if(!state.tombAt(i)) r+=mixHash(FNV(state.hashAt(i),FNV(state.entryAt(i).v.toHash(),fnvb)));
		return r;
	}

	void clear(){ state=null; } // like assigning null to a built-in AA
	HashMap dup(){
		HashMap r;
		if(!state) return r;
		r.state=new State;
		static if(stable){
			r.state.chunks=new E[][](state.chunks.length);
			r.state.tombs=new ubyte[][](state.tombs.length);
			foreach(i;0..state.chunks.length){
				r.state.chunks[i]=new E[](State.chunkLength(i));
				r.state.tombs[i]=state.tombs[i].dup;
				auto base=State.chunkStart(i);
				auto n=min(State.chunkLength(i),state.eused-base);
				foreach(j;0..n) copyEmplace(state.chunks[i][j], r.state.chunks[i][j]); // honor copy constructors
			}
		}else{
			r.state.ealloc=new E[](state.eused);
			foreach(i;0..state.eused) copyEmplace(state.ealloc[i], r.state.ealloc[i]); // honor copy constructors
			r.state.tombstone=state.tombstone[0..state.eused].dup;
			static if(!stable) r.state.tombstones=state.tombstones;
		}
		r.state.eused=state.eused;
		r.state.index=state.index.dup;
		r.state.length=state.length;
		r.state.deletedSlots=state.deletedSlots;
		return r;
	}

	//static if(is(typeof(text(K.init,V.init))))
	string toString(){
		auto r="[";
		foreach(k,v;this) r~=text(k,":",v)~", ";
		if(r.length>2) r=r[0..$-2];
		r~="]";
		return r;
	}
}

/+ Read-modify-write of the entry for k in m that computes the hash of k and probes
 the table only once (cf. Haskell's Data.Map.alter). f receives the current value
 (none!V if k is absent) and returns the new one: just(v) stores v under k, none!V
 removes k (or leaves it absent). f must not access m.
 Example: m.alter!(old=>just((old?old.get:0)+1))(k);
 (This is not a member function so that f can be a local lambda.) +/
import std.traits:TemplateOf,isScalarType,isIntegral,isSomeChar;
void alter(alias f,M,K)(ref M m,K key)if(__traits(isSame,TemplateOf!M,HashMap)&&is(K:M.K)&&!is(M.V==void[0])){
	alias V=M.V, E=M.E;
	M.K k=key;
	immutable hk=m.h(k);
	size_t s,p;
	auto state=m.state;
	immutable probed=state&&state.index.length;
	immutable found=probed&&state.probe(k,hk,s,p);
	Maybe!V nv=f(found?just(state.entryAt(p).v):none!V);
	if(found){
		if(nv) state.entryAt(p).v=move(nv.get());
		else state.removeAt(s,p);
		return;
	}
	if(!nv) return;
	m.ensureState().insertAbsent(E(move(nv.get()),k),hk,s,probed);
}

import std.range;
struct HSet(T_,alias eq, alias h, Storage storage_=Storage.compact, bool storeHash_=true){
	alias T=T_;
	private HashMap!(T,void[0],eq,h,storage_,storeHash_) payload;
	void clear(){ payload.clear(); }
	auto dup(){ return HSet(payload.dup); }
	@property size_t length(){ return payload.length; }
	hash_t toHash(){
		auto st=payload.state;
		if(!st) return 0;
		hash_t r=0;
		foreach(i;0..st.eused) if(!st.tombAt(i)) r+=mixHash(FNV(st.hashAt(i))); // (=h(x))
		return r;
	}
	bool opBinaryRight(string op: "in")(T t){
		return t in payload;
	}
	void insert(T t){
		bool isNew;
		payload.ensureState().insert(typeof(payload).E(t),isNew);
	}
	void opIndexAssign(void[0] v, T t){ insert(t); }
	void remove(T t){
		payload.remove(t);
	}
	int opApply(scope int delegate(T) dg){
		foreach(x,_;payload) if(auto r=dg(x)) return r;
		return 0;
	}
	bool opEquals(ref HSet rhs){
		return payload==rhs.payload;
	}
	static if(is(typeof(text(T.init)))) string toString(){
		string r="{";
		foreach(x;this) r~=text(x)~", ";
		if(r.length>2) r=r[0..$-2];
		return r~="}";
	}
}

template hset(alias h,alias eq){
	auto hset(T)(T args){
		alias S=typeof({ foreach(x;args) return x; assert(0); }());
		HSet!(S,eq,h) s;
		foreach(x;args) s.insert(x);
		return s;
	}
}

struct SHSet(T_, Storage storage_=Storage.compact) if(is(T_==class)){ // small hash set
	alias T=T_;
	bool isSmall=true;
	union{ T[4] small; HSet!(T,(a,b)=>a is b,a=>a.toHash(),storage_) large; }
	private this(typeof(large) large){ isSmall=false; this.large=large; }
	void clear(){
		if(isSmall) small[]=null;
		else large.clear();
	}
	auto dup(){
		if(isSmall) return this;
		return SHSet(large.dup);
	}
	@property size_t length(){
		if(isSmall){ size_t r=0; foreach(x;small) if(x !is null) r++; return r; }
		return large.length;
	}
	hash_t toHash(){
		if(isSmall){ hash_t r; foreach(x;small) if(x !is null) r+=mixHash(FNV(x.toHash())); return r; }
		return large.toHash();
	}
	bool opBinaryRight(string op: "in")(T t){
		if(isSmall){ foreach(x;small) if(x is t) return true; return false; }
		return t in large;
	}
	void insert(T t){
		if(isSmall){
			foreach(x;small) if(x is t) return;
			foreach(ref x;small) if(x is null){ x=t; return; }
			typeof(large) l;
			foreach(x;small) l.insert(x);
			isSmall=false;
			large=l;
		}
		large.insert(t);
	}
	void opIndexAssign(void[0] v, T t){ insert(t); }
	void remove(T t){
		if(isSmall){
			foreach(ref x;small) if(x is t) x=null;
			return;
		}
		large.remove(t);
		if(large.length<=small.length){
			T[small.length] s;
			int i=0;
			foreach(x;large) s[i++]=x;
			isSmall=true;
			small=s;
		}
	}
	int opApply(scope int delegate(T) dg){
		if(isSmall){ foreach(x;small) if(x !is null) if(auto r=dg(x)) return r; return 0; }
		foreach(x;large) if(auto r=dg(x)) return r;
		return 0;
	}
	bool opEquals(ref SHSet rhs){
		foreach(x;this) if(x !in rhs) return false;
		foreach(x;rhs) if(x !in this) return false;
		return true;
	}
	static if(is(typeof(text(T.init)))) string toString(){
		string r="{";
		foreach(x;this) r~=text(x)~", ";
		if(r.length>2) r=r[0..$-2];
		return r~="}";
	}
}

auto shset(T)(T args){
	alias S=typeof({ foreach(x;args) return x; assert(0); }());
	SHSet!S s;
	foreach(x;args) s.insert(x);
	return s;
}




/+
void main(){
	import std.stdio;
	auto s=hset!(a=>a,(a,b)=>a==b,int)([1,2,3,4]);
	writeln(3 in s);
	auto t=hset!(a=>a.toHash(),(a,b)=>a==b)([s]);
	writeln(s !in t);
}+/

struct Subsets(T){
	typeof(T.init.array) arr;
	int opApply(scope int delegate(T) dg){
		T cur;
		int enumerate(size_t i){
			if(i>=arr.length) return dg(cur.dup);
			if(auto r=enumerate(i+1)) return r;
			cur.insert(arr[i]);
			if(auto r=enumerate(i+1)) return r;
			cur.remove(arr[i]);
			return 0;
		}
		return enumerate(0);
	}
}

auto subsets(T)(T arg){ return Subsets!T(arg.array); }
auto element(T)(T arg)in{assert(arg.length==1);}do{ foreach(x;arg) return x; assert(0); }

T intersect(T)(T a,T b){
	T r;
	foreach(x;a) if(x in b) r.insert(x);
	return r;
}
T unite(T)(T a,T b){
	T r;
	foreach(x;a) r.insert(x);
	foreach(y;b) r.insert(y);
	return r;
}

T setMinus(T)(T a,T b){
	T r;
	foreach(x;a) if(x !in b) r.insert(x);
	return r;
}

