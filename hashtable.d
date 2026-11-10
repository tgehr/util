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
		static if(!stable) uint keepPositions; // (no compaction while an iteration relies on the positions, see `LayeredMap.opApply`)

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
				auto size=index.length;
				while(size>initialIndexSize&&10*(length+1)<=7*(size/4)) size/=2; // (after many removals)
				rehash(size);
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
			static if(!stable){
				if(tombstones>length+8&&!keepPositions){ // (also when insertions reuse the deleted index slots, e.g., of entries that are removed and inserted again)
					compactEntries();
					return true;
				}
			}
			if(10*(length+deletedSlots+1)>7*index.length){
				static if(!stable){
					if(tombstones*2>length+1&&!keepPositions){
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
	bool tryGetPosition(K k,out size_t pos){ // (of the entry for k in the iteration order; compacting changes the positions, but not their order)
		size_t s;
		return state&&state.probe(k,s,pos);
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
	HashMap dup(size_t room=0){ // (`room`: for entries inserted into the copy later)
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
			r.state.ealloc=new E[](state.eused+room);
			foreach(i;0..state.eused) copyEmplace(state.ealloc[i], r.state.ealloc[i]); // honor copy constructors
			r.state.tombstone=new ubyte[](state.eused+room);
			r.state.tombstone[0..state.eused]=state.tombstone[0..state.eused];
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

V identityCopy(V)(ref V v){ return v; } // (the default of `LayeredMap`)

/+ A map with the semantics of `HashMap` with compact storage (iteration in the order of insertion, where assigning to
 a key that is present keeps its place). A large map is layered: its copies share a base that is never changed, and a
 copy only copies the entries that changed since the base was built, see `dup`. A small map is a `HashMap`, see
 `needsRebase`. `copyValue` copies a value that a copy must not share. +/
struct LayeredMap(K_, V_, alias eq_, alias h_, alias copyValue=identityCopy){
	alias K=K_;
	alias V=V_;
	private alias Table=HashMap!(K,V,eq_,h_);
	private static struct Change{
		V v;
		size_t pos; // (of the key in the base, or `fresh` for an entry inserted after the base was built)
		bool removed;
	}
	private enum size_t fresh=size_t.max;
	private enum size_t smallSize=32; // (a map with at most twice as many entries is not layered: a copy of all of them costs about as much as the lookups in both layers save)
	private static final class Base{
		Table table;
		Object cache; // (of the user, for the entries of the base, see `baseCache`)
	}
	private static final class Layers{ // (of a layered map, or of one that logs its changes)
		Base base; // (`null`: not layered, see `plain`)
		HashMap!(K,Change,eq_,h_) delta;
		size_t length; // (of a layered map)
		uint iterating; // (no new base while the entries are iterated)
		K[] log; // (the keys of the changed entries since `startLog`)
		bool logging;
	}
	private Table plain; // (the entries of a map that is not layered)
	private Layers layers;
	private size_t changes; // (also of the copies it was copied from)

	private @property Base base(){ pragma(inline,true); return layers?layers.base:null; }
	@property size_t length(){ pragma(inline,true); return base?layers.length:plain.length; }
	@property bool isLayered(){ pragma(inline,true); return !!base; }
	@property size_t numChanges()const{ return changes; } // (equal for a copy and the map it was copied from while neither changes)
	void startLog(K[] initial=null){
		if(!layers) layers=new Layers;
		layers.logging=true;
		layers.log=initial;
	}
	void stopLog(){
		if(!layers) return;
		layers.logging=false;
		layers.log=null;
		if(!layers.base) layers=null;
	}
	@property bool isLogging(){ return layers&&layers.logging; }
	@property K[] changeLog(){ return layers?layers.log:null; } // (in the order of the changes, with repetitions, also of the entries that changed back; a copy does not log)
	private void noteChange(K k){
		pragma(inline,true);
		changes++;
		if(layers&&layers.logging) layers.log~=k;
	}

	private Change* findChange(K k){
		return layers.delta.findPtr(k);
	}
	private bool basePosition(K k,out size_t pos){
		size_t s;
		return layers.base.table.state&&layers.base.table.state.probe(k,s,pos);
	}
	bool opBinaryRight(string op: "in")(K k){
		pragma(inline,true);
		if(!base) return k in plain;
		return hasLayered(k);
	}
	private bool hasLayered(K k){
		if(auto c=findChange(k)) return !c.removed;
		size_t pos;
		return basePosition(k,pos);
	}
	V get(K k, lazy V alt){
		pragma(inline,true);
		if(!base) return plain.get(k,alt);
		bool found;
		auto v=getLayered(k,found);
		return found?v:alt;
	}
	private V getLayered(K k,out bool found){
		if(auto c=findChange(k)){
			found=!c.removed;
			return found?c.v:V.init;
		}
		size_t pos;
		if(basePosition(k,pos)){
			found=true;
			return layers.base.table.state.entryAt(pos).v;
		}
		return V.init;
	}
	V opIndex(K k){
		pragma(inline,true);
		if(!base) return plain[k];
		return indexLayered(k);
	}
	private V indexLayered(K k){
		if(auto c=findChange(k)){
			if(!c.removed) return c.v;
		}else{
			size_t pos;
			if(basePosition(k,pos)) return layers.base.table.state.entryAt(pos).v;
		}
		static if(is(typeof(text(k)))) assert(0, text("key not found: ",k));
		else assert(0, "key not found");
	}
	void opIndexAssign(V v, K k){
		pragma(inline,true);
		noteChange(k);
		if(!base){
			plain[k]=v;
			return;
		}
		assignLayered(v,k);
	}
	private void assignLayered(V v,K k){
		if(auto c=findChange(k)){
			if(!c.removed){ c.v=v; return; }
			layers.delta.remove(k); // (inserted again after it was removed: it moves to the end)
			layers.delta[k]=Change(v,fresh,false);
			layers.length++;
			return;
		}
		size_t pos;
		if(basePosition(k,pos)){
			layers.delta[k]=Change(v,pos,false);
			return;
		}
		layers.delta[k]=Change(v,fresh,false);
		layers.length++;
	}
	bool remove(K k){
		pragma(inline,true);
		noteChange(k);
		if(!base) return plain.remove(k);
		return removeLayered(k);
	}
	private bool removeLayered(K k){
		size_t pos;
		if(auto c=findChange(k)){
			if(c.removed) return false;
			if(c.pos!=fresh){
				c.removed=true;
				c.v=V.init;
			}else{
				layers.delta.remove(k);
				if(basePosition(k,pos)) layers.delta[k]=Change(V.init,pos,true); // (inserted again after it was removed from the base)
			}
			layers.length--;
			return true;
		}
		if(!basePosition(k,pos)) return false;
		layers.delta[k]=Change(V.init,pos,true);
		layers.length--;
		return true;
	}
	void clear(){
		changes++;
		if(isLogging) foreach(k,ref v;this) layers.log~=k;
		plain.clear();
		if(!layers) return;
		layers.base=null;
		layers.delta.clear();
		layers.length=0;
		if(!layers.logging) layers=null;
	}
	@property size_t positionLimit(){ // (all positions are smaller)
		if(!base) return plain.state?plain.state.eused:0;
		return (layers.base.table.state?layers.base.table.state.eused:0)+(layers.delta.state?layers.delta.state.eused:0);
	}
	bool tryGetPosition(K k,out size_t pos){ // (of the entry for k in the iteration order)
		pragma(inline,true);
		if(!base) return plain.tryGetPosition(k,pos);
		return positionLayered(k,pos);
	}
	private bool positionLayered(K k,out size_t pos){
		if(auto c=findChange(k)){
			if(c.removed) return false;
			if(c.pos!=fresh){ pos=c.pos; return true; }
			size_t dpos;
			if(!layers.delta.tryGetPosition(k,dpos)) return false;
			pos=(layers.base.table.state?layers.base.table.state.eused:0)+dpos;
			return true;
		}
		return basePosition(k,pos);
	}
	private void rebase(){ // (a new base with all entries, or none, see `needsRebase`)
		auto n=length;
		if(!base){ // (its values are only in the new base)
			auto nbase=new Base;
			nbase.table=plain;
			plain=Table.init;
			if(!layers) layers=new Layers;
			layers.base=nbase;
			layers.length=n;
			return;
		}
		Table table;
		foreach(k,v;this) table[k]=copyValue(v);
		layers.delta.clear();
		if(n<=smallSize){
			layers.base=null;
			plain=table;
			if(!layers.logging) layers=null;
			return;
		}
		auto nbase=new Base;
		nbase.table=table;
		layers.base=nbase;
	}
	private bool needsRebase(){
		import std.math: sqrt;
		if(!base) return plain.length>2*smallSize&&!plain.state.keepPositions; // (not while it is iterated, see `opApply`)
		if(layers.length<=smallSize) return true;
		return layers.delta.length>16+2*cast(size_t)sqrt(cast(double)layers.base.table.length);
	}
	LayeredMap dup(){ // (of a layered map proportional to the number of changed entries)
		if(!(layers&&layers.iterating)&&needsRebase()) rebase();
		LayeredMap r;
		r.changes=changes;
		if(!base){
			r.plain=plain.dup();
			static if(!__traits(isSame,copyValue,identityCopy)) foreach(ref v;r.plain) v=copyValue(v);
			return r;
		}
		r.layers=new Layers;
		r.layers.base=layers.base;
		r.layers.delta=layers.delta.dup(layers.delta.length/4+4);
		static if(!__traits(isSame,copyValue,identityCopy)) foreach(ref c;r.layers.delta) if(!c.removed) c.v=copyValue(c.v);
		r.layers.length=layers.length;
		return r;
	}
	V* own(K k){ // (the value for `k` that this map does not share with its copies, valid until the next change; `null` if there is none; see `noteChanged`)
		pragma(inline,true);
		if(!base) return plain.findPtr(k);
		return ownLayered(k);
	}
	private V* ownLayered(K k){
		if(auto c=findChange(k)) return c.removed?null:&c.v;
		size_t pos;
		if(!basePosition(k,pos)) return null;
		layers.delta[k]=Change(copyValue(layers.base.table.state.entryAt(pos).v),pos,false);
		return &findChange(k).v;
	}
	void noteChanged(K k){ pragma(inline,true); noteChange(k); } // (the caller changes the value that `own` returns)
	bool owns(K k){ // (whether the value for `k` is not shared with the base)
		pragma(inline,true);
		if(!base) return k in plain;
		return !!findChange(k);
	}
	Object* baseCache(){ return base?&layers.base.cache:null; } // (for the entries of the base, which never change)
	int opApplyBase(scope int delegate(K,V) dg){ // (the entries of the base, also those that this map changed)
		if(base) foreach(k,v;layers.base.table) if(auto r=dg(k,v)) return r;
		return 0;
	}
	int opApplyOwned(scope int delegate(K,ref V) dg)in{ // (the entries of a map that is not layered, which may be changed through the references: each counts as changed, see `noteChanged`)
		assert(!base);
	}do{
		auto pstate=plain.state;
		if(!pstate) return 0;
		immutable n=pstate.eused;
		pstate.keepPositions++;
		scope(exit) pstate.keepPositions--;
		foreach(i;0..n){
			if(pstate.tombAt(i)) continue;
			auto k=pstate.entryAt(i).k;
			noteChange(k);
			if(auto r=dg(k,pstate.entryAt(i).v)) return r;
		}
		return 0;
	}
	int opApplyChanged(scope int delegate(K) dg){ // (the keys whose entries may differ from those of the base)
		if(!base){
			foreach(k,ref v;plain) if(auto r=dg(k)) return r;
			return 0;
		}
		foreach(k,ref c;layers.delta) if(auto r=dg(k)) return r;
		return 0;
	}
	int opApply(scope int delegate(ref V) dg){
		return opApply((ref K k,ref V v)=>dg(v));
	}
	int opApply(scope int delegate(ref K,ref V) dg){ // (assignments to the values are written back)
		if(!base){
			auto pstate=plain.state;
			if(!pstate) return 0;
			immutable n=pstate.eused; // (as for `HashMap`: not the entries inserted by the loop body)
			pstate.keepPositions++;
			scope(exit) pstate.keepPositions--;
			foreach(i;0..n){
				if(pstate.tombAt(i)) continue;
				K k=pstate.entryAt(i).k;
				V v=pstate.entryAt(i).v;
				auto old=v;
				auto r=dg(k,v);
				if(v !is old) this[k]=v;
				if(r) return r;
			}
			return 0;
		}
		auto l=layers;
		l.iterating++;
		scope(exit) l.iterating--;
		auto dstate=l.delta.state;
		immutable n=dstate?dstate.eused:0; // (as for `HashMap`: not the entries inserted by the loop body)
		if(dstate) dstate.keepPositions++;
		scope(exit) if(dstate) dstate.keepPositions--;
		if(l.base.table.state){
			auto bstate=l.base.table.state;
			foreach(i;0..bstate.eused){
				if(bstate.tombAt(i)) continue;
				K k=bstate.entryAt(i).k;
				V v;
				if(auto c=findChange(k)){
					if(c.removed||c.pos==fresh) continue;
					v=c.v;
				}else v=bstate.entryAt(i).v;
				auto old=v;
				auto r=dg(k,v);
				if(v !is old) this[k]=v;
				if(r) return r;
			}
		}
		if(dstate){
			foreach(i;0..n){
				if(dstate.tombAt(i)) continue;
				auto c=&dstate.entryAt(i).v;
				if(c.removed||c.pos!=fresh) continue;
				K k=dstate.entryAt(i).k;
				V v=c.v;
				auto old=v;
				auto r=dg(k,v);
				if(v !is old) this[k]=v;
				if(r) return r;
			}
		}
		return 0;
	}
	@property V[] values(){
		auto r=new V[](length);
		size_t i=0;
		foreach(v;this) r[i++]=v;
		return r;
	}
	@property V[] byValue(){ return values; }
	@property K[] keys(){
		auto r=new K[](length);
		size_t i=0;
		foreach(k,v;this) r[i++]=k;
		return r;
	}
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

/+ A map with the semantics of `HashMap` with compact storage (iteration in the order of insertion, where assigning to a
 key that is present keeps its place, and a key inserted again after its removal moves to the end), whose copies share
 their entries: a copy takes constant time, and a change copies the nodes on the path to its entry in a hash trie, so
 that the copies of a map, e.g., the tables of nested scopes, only take memory for the entries that they change. +/
struct PersistentMap(K_, V_, alias eq_, alias h_){
	import core.memory: GC;
	import core.bitop: popcnt;
	alias K=K_;
	alias V=V_;
	private static struct Entry{
		K k;
		V v;
		size_t pos; // (the order of the entries, see `nextPos`)
	}
	private enum bits=4,width=1<<bits,hashBits=64;
	private static struct Node{ // (followed by its entries and then its children, in the order of their slots)
		ushort dataMap,nodeMap; // (the slots that hold an entry, and those that hold a child)
		uint numCollisions; // (of a node below the last level of the hash: its entries have equal hashes)
		Owner owner; // (the only map that refers to it, if it is the map's `owner`: that map changes it in place)
	}
	private static final class Owner{
		bool copied; // (the map was copied: the copies share its nodes)
	}
	private Node* root;
	private Owner owner; // (of the nodes that only this map refers to; none after a copy, see `dup`)
	this(this){ // (a copy that shares the entries: neither changes the nodes in place any more, see `owner`)
		if(!owner) return;
		owner.copied=true;
		owner=null;
	}
	private size_t length_;
	private size_t nextPos; // (of the next key that is inserted)
	private size_t changes; // (also of the copies it was copied from)
	private static final class Log{
		K[] keys; // (of the changed entries since `startLog`)
	}
	private Log log;

	private static ulong hashKey(K k){
		ulong h=h_(k);
		h^=h>>33;
		h*=0xff51afd7ed558ccdUL;
		h^=h>>33;
		h*=0xc4ceb9fe1a85ec53UL;
		h^=h>>33;
		return h;
	}
	private static uint slot(ulong h,uint shift){ return cast(uint)(h>>shift)&(width-1); }
	private static size_t index(uint map,uint bit){ return popcnt(map&(bit-1)); }
	private static size_t numData(const(Node)* n){ return n.nodeMap==0&&n.numCollisions?n.numCollisions:popcnt(n.dataMap); }
	private static size_t numChildren(const(Node)* n){ return popcnt(n.nodeMap); }
	private static Entry* entries(Node* n){ return cast(Entry*)(cast(ubyte*)n+Node.sizeof); }
	private static Node** children(Node* n){ return cast(Node**)(cast(ubyte*)n+Node.sizeof+numData(n)*Entry.sizeof); }
	private static Node* allocNode(ushort dataMap,ushort nodeMap,uint numCollisions,Owner owner){
		auto nd=nodeMap==0&&numCollisions?numCollisions:popcnt(dataMap);
		auto n=cast(Node*)GC.calloc(Node.sizeof+nd*Entry.sizeof+popcnt(nodeMap)*(Node*).sizeof);
		n.dataMap=dataMap;
		n.nodeMap=nodeMap;
		n.numCollisions=numCollisions;
		n.owner=owner;
		return n;
	}

	private static Entry* find(Node* n,K k,ulong h){
		for(uint shift=0;n;shift+=bits){
			if(shift>=hashBits){
				foreach(ref e;entries(n)[0..n.numCollisions]) if(eq_(e.k,k)) return &e;
				return null;
			}
			auto bit=1u<<slot(h,shift);
			if(n.dataMap&bit){
				auto e=&entries(n)[index(n.dataMap,bit)];
				return eq_(e.k,k)?e:null;
			}
			if(!(n.nodeMap&bit)) return null;
			n=children(n)[index(n.nodeMap,bit)];
		}
		return null;
	}
	private static Node* single(ref Entry e,ulong h,uint shift,Owner o){
		if(shift>=hashBits){
			auto r=allocNode(0,0,1,o);
			entries(r)[0]=e;
			return r;
		}
		auto r=allocNode(cast(ushort)(1u<<slot(h,shift)),0,0,o);
		entries(r)[0]=e;
		return r;
	}
	private static Node* pair(ref Entry a,ulong ha,ref Entry b,ulong hb,uint shift,Owner o){ // (a node with both entries, whose hashes agree below `shift`)
		if(shift>=hashBits){
			auto r=allocNode(0,0,2,o);
			entries(r)[0]=a;
			entries(r)[1]=b;
			return r;
		}
		auto sa=slot(ha,shift),sb=slot(hb,shift);
		if(sa==sb){
			auto r=allocNode(0,cast(ushort)(1u<<sa),0,o);
			children(r)[0]=pair(a,ha,b,hb,shift+bits,o);
			return r;
		}
		auto r=allocNode(cast(ushort)((1u<<sa)|(1u<<sb)),0,0,o);
		if(sa<sb){ entries(r)[0]=a; entries(r)[1]=b; }
		else{ entries(r)[0]=b; entries(r)[1]=a; }
		return r;
	}
	private static Node* withEntry(Node* n,uint bit,ref Entry e,Owner o){ // (a copy of `n` with `e` in the free slot `bit`)
		auto r=allocNode(cast(ushort)(n.dataMap|bit),n.nodeMap,0,o);
		auto i=index(n.dataMap,bit),nd=numData(n);
		auto re=entries(r),ne=entries(n);
		re[0..i]=ne[0..i];
		re[i]=e;
		re[i+1..nd+1]=ne[i..nd];
		children(r)[0..numChildren(n)]=children(n)[0..numChildren(n)];
		return r;
	}
	private static Node* withChild(Node* n,uint bit,Node* c,Owner o){ // (a copy of `n` with the child `c` in place of its entry in the slot `bit`)
		auto r=allocNode(cast(ushort)(n.dataMap&~bit),cast(ushort)(n.nodeMap|bit),0,o);
		auto i=index(n.dataMap,bit),nd=numData(n);
		auto re=entries(r),ne=entries(n);
		re[0..i]=ne[0..i];
		re[i..nd-1]=ne[i+1..nd];
		auto j=index(n.nodeMap,bit),nc=numChildren(n);
		auto rc=children(r),nc_=children(n);
		rc[0..j]=nc_[0..j];
		rc[j]=c;
		rc[j+1..nc+1]=nc_[j..nc];
		return r;
	}
	private static Node* own(Node* n,Owner o){ // (`n`, or a copy of it that `o` owns)
		if(n.owner is o) return n;
		auto r=allocNode(n.dataMap,n.nodeMap,n.numCollisions,o);
		auto nd=numData(n),nc=numChildren(n);
		entries(r)[0..nd]=entries(n)[0..nd];
		children(r)[0..nc]=children(n)[0..nc];
		return r;
	}
	private static Node* insert(Node* n,ref Entry e,ulong h,uint shift,Owner o,out bool found){ // (`found`: the key was present, and keeps its position)
		if(!n) return single(e,h,shift,o);
		if(shift>=hashBits){
			foreach(i,ref x;entries(n)[0..n.numCollisions]){
				if(!eq_(x.k,e.k)) continue;
				found=true;
				auto r=own(n,o);
				entries(r)[i].v=e.v;
				return r;
			}
			auto r=allocNode(0,0,n.numCollisions+1,o);
			entries(r)[0..n.numCollisions]=entries(n)[0..n.numCollisions];
			entries(r)[n.numCollisions]=e;
			return r;
		}
		auto bit=1u<<slot(h,shift);
		if(n.dataMap&bit){
			auto i=index(n.dataMap,bit);
			auto x=&entries(n)[i];
			if(eq_(x.k,e.k)){
				found=true;
				if(x.v is e.v) return n;
				auto r=own(n,o);
				entries(r)[i].v=e.v;
				return r;
			}
			auto c=pair(*x,hashKey(x.k),e,h,shift+bits,o);
			return withChild(n,bit,c,o);
		}
		if(n.nodeMap&bit){
			auto j=index(n.nodeMap,bit);
			auto c=insert(children(n)[j],e,h,shift+bits,o,found);
			if(c is children(n)[j]) return n;
			auto r=own(n,o);
			children(r)[j]=c;
			return r;
		}
		return withEntry(n,bit,e,o);
	}
	private static bool isSingle(Node* n){ return n.nodeMap==0&&numData(n)==1; }
	private static Node* remove(Node* n,K k,ulong h,uint shift,Owner o,out bool removed){ // (`null` if it has no entries left)
		if(!n) return null;
		if(shift>=hashBits){
			foreach(i,ref x;entries(n)[0..n.numCollisions]){
				if(!eq_(x.k,k)) continue;
				removed=true;
				if(n.numCollisions==1) return null;
				auto r=allocNode(0,0,n.numCollisions-1,o);
				entries(r)[0..i]=entries(n)[0..i];
				entries(r)[i..n.numCollisions-1]=entries(n)[i+1..n.numCollisions];
				return r;
			}
			return n;
		}
		auto bit=1u<<slot(h,shift);
		if(n.dataMap&bit){
			auto i=index(n.dataMap,bit);
			if(!eq_(entries(n)[i].k,k)) return n;
			removed=true;
			if(n.dataMap==bit&&!n.nodeMap) return null;
			auto r=allocNode(cast(ushort)(n.dataMap&~bit),n.nodeMap,0,o);
			auto nd=numData(n);
			entries(r)[0..i]=entries(n)[0..i];
			entries(r)[i..nd-1]=entries(n)[i+1..nd];
			children(r)[0..numChildren(n)]=children(n)[0..numChildren(n)];
			return r;
		}
		if(!(n.nodeMap&bit)) return n;
		auto j=index(n.nodeMap,bit);
		auto c=remove(children(n)[j],k,h,shift+bits,o,removed);
		if(!removed) return n;
		if(c&&!isSingle(c)){
			if(c is children(n)[j]) return n;
			auto r=own(n,o);
			children(r)[j]=c;
			return r;
		}
		if(!c&&n.nodeMap==bit&&!n.dataMap) return null;
		// (the child is gone or holds a single entry, which moves into this node, as the trie stays canonical)
		auto r=allocNode(cast(ushort)(c?n.dataMap|bit:n.dataMap),cast(ushort)(n.nodeMap&~bit),0,o);
		auto nd=numData(n);
		auto re=entries(r),ne=entries(n);
		if(c){
			auto i=index(n.dataMap,bit);
			re[0..i]=ne[0..i];
			re[i]=entries(c)[0];
			re[i+1..nd+1]=ne[i..nd];
		}else re[0..nd]=ne[0..nd];
		auto nc=numChildren(n);
		auto rc=children(r),nc_=children(n);
		rc[0..j]=nc_[0..j];
		rc[j..nc-1]=nc_[j+1..nc];
		return r;
	}
	private static void collect(Node* n,Entry[] r,ref size_t i){
		if(!n) return;
		auto nd=numData(n);
		r[i..i+nd]=entries(n)[0..nd];
		i+=nd;
		foreach(c;children(n)[0..numChildren(n)]) collect(c,r,i);
	}
	private Entry[] sorted(){ // (the entries in the order of the map: a radix sort by position)
		auto r=new Entry[](length_);
		size_t i=0;
		collect(root,r,i);
		assert(i==length_);
		if(length_<=32){
			import std.algorithm: sort;
			sort!((a,b)=>a.pos<b.pos)(r);
			return r;
		}
		enum digit=8,radix=1<<digit;
		auto t=new Entry[](length_);
		size_t[radix] counts;
		for(uint shift=0;shift<64&&(nextPos-1)>>shift;shift+=digit){
			counts[]=0;
			foreach(ref e;r) counts[(e.pos>>shift)&(radix-1)]++;
			size_t sum=0;
			foreach(ref c;counts){ auto x=c; c=sum; sum+=x; }
			foreach(ref e;r) t[counts[(e.pos>>shift)&(radix-1)]++]=e;
			auto tmp=r; r=t; t=tmp;
		}
		return r;
	}

	@property size_t length(){ return length_; }
	@property size_t numChanges()const{ return changes; } // (equal for a copy and the map it was copied from while neither changes)
	void startLog(K[] initial=null){
		if(!log) log=new Log;
		log.keys=initial;
	}
	void stopLog(){ log=null; }
	@property bool isLogging(){ return !!log; }
	@property K[] changeLog(){ return log?log.keys:null; } // (in the order of the changes, with repetitions, also of the entries that changed back; a copy does not log)
	private void noteChange(K k){
		pragma(inline,true);
		changes++;
		if(log) log.keys~=k;
	}
	bool opBinaryRight(string op: "in")(K k){ return !!find(root,k,hashKey(k)); }
	V get(K k, lazy V alt){
		if(auto e=find(root,k,hashKey(k))) return e.v;
		return alt;
	}
	V opIndex(K k){
		if(auto e=find(root,k,hashKey(k))) return e.v;
		import std.conv: text;
		static if(is(typeof(text(k)))) assert(0, text("key not found: ",k));
		else assert(0, "key not found");
	}
	void opIndexAssign(V v, K k){
		noteChange(k);
		auto e=Entry(k,v,nextPos);
		bool found;
		if(!owner||owner.copied) owner=new Owner;
		root=insert(root,e,hashKey(k),0,owner,found);
		if(!found){
			nextPos++;
			length_++;
		}
	}
	bool remove(K k){
		noteChange(k);
		bool removed;
		if(!owner||owner.copied) owner=new Owner;
		root=remove(root,k,hashKey(k),0,owner,removed);
		if(removed) length_--;
		return removed;
	}
	void clear(){
		changes++;
		if(log) foreach(ref e;sorted()) log.keys~=e.k;
		root=null;
		length_=0;
	}
	@property size_t positionLimit(){ return nextPos; } // (all positions are smaller)
	bool tryGetPosition(K k,out size_t pos){ // (of the entry for k in the iteration order)
		if(auto e=find(root,k,hashKey(k))){
			pos=e.pos;
			return true;
		}
		return false;
	}
	PersistentMap dup(){
		owner=null;
		PersistentMap r;
		r.root=root;
		r.length_=length_;
		r.nextPos=nextPos;
		r.changes=changes;
		return r;
	}
	int opApply(scope int delegate(ref V) dg){
		return opApply((ref K k,ref V v)=>dg(v));
	}
	int opApply(scope int delegate(ref K,ref V) dg){ // (the entries at the start, in their order, unless they were removed before their turns; assignments to the values are written back)
		auto start=changes;
		foreach(ref e;sorted()){
			V v=e.v;
			if(changes!=start){ // (the map changed since the start)
				auto cur=find(root,e.k,hashKey(e.k));
				if(!cur||cur.pos!=e.pos) continue;
				v=cur.v;
			}
			K k=e.k;
			auto old=v;
			auto r=dg(k,v);
			if(v !is old) this[k]=v;
			if(r) return r;
		}
		return 0;
	}
	auto byValue(){
		import std.algorithm: map;
		return sorted().map!(e=>e.v);
	}
	@property V[] values(){
		import std.algorithm: map;
		import std.array: array;
		return sorted().map!(e=>e.v).array;
	}
	@property K[] keys(){
		import std.algorithm: map;
		import std.array: array;
		return sorted().map!(e=>e.k).array;
	}
	string toString(){
		import std.conv: text;
		auto r="[";
		foreach(k,v;this) r~=text(k,":",v)~", ";
		if(r.length>2) r=r[0..$-2];
		r~="]";
		return r;
	}
	size_t censusNodes(scope bool delegate(const(void)*) seen){ // (the bytes of the nodes that `seen` did not see yet)
		size_t r=0;
		void visit(Node* n){
			if(!n||seen(n)) return;
			r+=GC.sizeOf(n);
			foreach(c;children(n)[0..numChildren(n)]) visit(c);
		}
		visit(root);
		return r;
	}
}
