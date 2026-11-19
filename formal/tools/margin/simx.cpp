// margin/simx.cpp (shard C, UNTRUSTED): a C++ port of tools/huff/simadv.py for the option subset margin.py uses.
//
//   python3 simx_conv.py NET.json BND.json NET.simx            (once per build)
//   KDEN=100 simx NET.simx --pairs P.. --corner 0 --kappa K --classes C.json --cdefault F --data0 --full
//        --R 400000 --su 1000 --datachange broad --nextreq seq --tmax T [--w W] [--dump D.json] [--maxev N]
//   build: g++ -O2 -std=c++17 -o simx simx.cpp
//
// Same semantics as simadv.py (transport, heap order (t, pri, seq), env reaction at each settled time, H_RUNT(w)
// read filter on LUT pins, exact rational delays for --classes), same stdout/stderr lines (RESULT, sim:, HRUNT,
// env:, out0), same exit codes (0 OK, 2 MISMATCH). Also accepted: --dout --dfall --reqgap --pipelined --pos/--seed
// (ignored without effect when --classes is given, as in simadv). Not ported: --gfrac, non---classes delay modes,
// --why/--watch/--trace, the non---full kernel cone. New: --maxev N: stop after N events, print no RESULT line,
// exit 3 (margin.py then records the run as ERROR/UNDECIDED, as for a memory cap hit). --want v1,v2,..: the expected
// out0 list (bench kernels: collatz, xorshift, ..) replaces gcd(a,b) per pair in the RESULT check; gcd is the default.
// Pair/out0 values are unsigned 64-bit. Undriven nodes (opaque outputs: FFs, LATCH-mode storage) stay at their
// initial value 0 unless the env drives them (bnd 'env' list / data bits), exactly as in simadv.
// DSP48E1 sites (margin/dsp/): gates with flag 2 in the .simx file evaluate the combinational DSP48E1 datapath
// (dsp48_p, = margin/dsp/dspmodel.py; simx --dsptest compares them); every input pin transport with its own arc.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <cmath>
#include <cctype>
#include <tuple>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <queue>
#include <utility>

using namespace std;
typedef long long ll;
typedef unsigned long long ull;

[[noreturn]] static void die(const char* fmt, const char* s = "") { fprintf(stderr, "simx: "); fprintf(stderr, fmt, s); fprintf(stderr, "\n"); exit(1); }

// ---------------- tiny JSON (for --classes) ----------------
struct JV { int ty = 0; string s; double num = 0; vector<JV> a; vector<pair<string, JV>> o; };  // ty 0 null 1 num 2 str 3 arr 4 obj 5 bool
struct JP {
    const char* p;
    void ws() { while (*p == ' ' || *p == '\n' || *p == '\r' || *p == '\t') p++; }
    string str() { string r; p++; while (*p && *p != '"') { if (*p == '\\') { p++; if (*p == 'n') r += '\n'; else r += *p; p++; } else r += *p++; } if (*p != '"') die("bad json string"); p++; return r; }
    JV val() {
        ws(); JV v;
        if (*p == '{') { v.ty = 4; p++; ws(); if (*p == '}') { p++; return v; }
            for (;;) { ws(); if (*p != '"') die("bad json key"); string k = str(); ws(); if (*p != ':') die("bad json"); p++; v.o.push_back({k, val()}); ws(); if (*p == ',') { p++; continue; } if (*p == '}') { p++; break; } die("bad json object"); } }
        else if (*p == '[') { v.ty = 3; p++; ws(); if (*p == ']') { p++; return v; }
            for (;;) { v.a.push_back(val()); ws(); if (*p == ',') { p++; continue; } if (*p == ']') { p++; break; } die("bad json array"); } }
        else if (*p == '"') { v.ty = 2; v.s = str(); }
        else if (!strncmp(p, "null", 4)) { p += 4; }
        else if (!strncmp(p, "true", 4)) { v.ty = 5; v.num = 1; p += 4; }
        else if (!strncmp(p, "false", 5)) { v.ty = 5; p += 5; }
        else { char* e; v.ty = 1; v.num = strtod(p, &e); if (e == p) die("bad json value"); p = e; }
        return v;
    }
};
static string slurp(const char* fn) {
    FILE* f = fopen(fn, "rb"); if (!f) die("cannot open %s", fn);
    string s; char buf[1 << 16]; size_t n; while ((n = fread(buf, 1, sizeof buf, f)) > 0) s.append(buf, n); fclose(f); return s;
}

// ---------------- netlist ----------------
static int NN, NGALL, NG, NCONEK, NSEEN;
static vector<string> names;
static vector<int> gk, gout, glut, gins0, ginit0;           // per simulated gate (in simadv's cone order)
static vector<int> ins;                                     // flattened inputs
static vector<ll> afmin, afmax, asmin, asmax;               // flattened arcs
static vector<uint64_t> initw;                              // flattened truth tables (64-bit words)
static vector<int> ds;                                      // flattened delays
static vector<double> his;                                  // flattened H_RUNT upper bounds (LUT gates)
static map<string, int> BN;
static vector<int> Bdata[3];                                // a_data, b_data, out0_data
static vector<int> XACKS;                                   // other input channels' acks (memory kernels), all waited for
struct XData { int ack; vector<int> nodes; };
static vector<XData> XDATA;                                 // operand channels between a and b (kernels with > 2 words)
struct HostP { string name; int req, we, ack; vector<int> addr, wdata; };
static vector<HostP> HOSTS;                                 // memory kernels: the host's port of each array (--hostport)

// DSP48E1 output-bit gates (flag 2 in the .simx file; margin/dsp/dsp_gates.py, model margin/dsp/dspmodel.py): the
// combinational DSP48E1 datapath (every register off; yosys cells_sim.v semantics), bit obit of P (= PCOUT).
// Inputs: data pins, role = port * 64 + bit (port 0 A_muxed, 1 B_muxed, 2 C, 3 PCIN); constant pins are in base[].
struct DspG { int obit, opm, alu, inm, cis, cin; ull base[4]; vector<int> roles; };
static vector<DspG> DSPG; static vector<int> gdsp;          // gdsp[g]: index into DSPG, or -1
// RAMB18E1 port A output bits (flag 3, margin/bram/bram_gates.py): one shared state per RAM (id), lazily stepped at the
// rising edges of its clock node; roles 0 clk (edge -> DO arc), 1 clk (edge at the pin: sampling), 2/3 WEA0/1,
// 16+i ADDR[4+i], 32+i DIADI[i]; WRITE_FIRST; setup / hold windows checked at the end (RAMVIOL).
struct RamG { int id, obit, ini; ull base; vector<int> roles; int su[3], ho[3]; vector<pair<int, unsigned>> mem; };
static vector<RamG> RAMG; static vector<int> gram;         // gram[g]: index into RAMG, or -1
struct RamS { int master = -1; vector<unsigned> mem; size_t ep = 0; vector<pair<ll, unsigned>> outs;
              vector<tuple<ll, int, bool>> edges; };    // outs: (edge time at the clock node, DO word); edges: (sample t, addr, wrote)
static vector<RamS> RAMS;
static const ull M48 = (1ULL << 48) - 1;
static inline ll sxt(ull v, int w) { v &= (1ULL << w) - 1; return (v >> (w - 1)) ? (ll)v - (1LL << w) : (ll)v; }
static ull dsp48_p(int opm, int alu, int inm, int cis, ull A, ull B, ull C, ull PCIN, int cin) {
    int x = opm & 3, y = (opm >> 2) & 3, z = (opm >> 4) & 7;
    ll am = (inm & 2) ? 0 : sxt(A, 25); ull m = (ull)(am * sxt(B, 18)) & M48;
    ull X = x == 0 ? 0 : x == 1 ? m : (((A & ((1ULL << 30) - 1)) << 18) | (B & ((1ULL << 18) - 1))) & M48;
    ull Y = y == 3 ? (C & M48) : y == 2 ? M48 : 0;
    ull Z = z == 0 ? 0 : z == 1 ? (PCIN & M48) : z == 3 ? (C & M48) : ((ull)sxt((PCIN & M48) >> 17, 31) & M48);
    if (x == 2 || (x == 1) != (y == 1) || z == 2 || z == 4 || z == 6 || z == 7 || cis != 0) die("dsp48: configuration not modelled");
    int ci = (alu & 12) ? 0 : (cin & 1);
    ull Zi = (alu & 1) ? (~Z & M48) : Z, sx = X ^ Y ^ Zi, cx = (X & Y) | (X & Zi) | (Y & Zi);
    ull s2 = (alu & 8) ? cx : sx, c2 = (alu & 4) ? 0 : cx;
    ull tot = (((c2 << 1) | (ull)ci) + s2) & M48;
    return (alu & 2) ? (~tot & M48) : tot;
}
static vector<int> gorig;
static void load_net(const char* fn) {
    string S = slurp(fn); const char* p = S.c_str(); char* e;
    if (strncmp(p, "SIMX1\n", 6)) die("%s: not a simx_conv.py file", fn);
    p += 6;
    NN = strtol(p, &e, 10); p = e; NGALL = strtol(p, &e, 10); p = e; NG = strtol(p, &e, 10); p = e;
    NCONEK = strtol(p, &e, 10); p = e; NSEEN = strtol(p, &e, 10); p = e; p++;
    names.resize(NN);
    for (int i = 0; i < NN; i++) { const char* q = strchr(p, '\n'); names[i].assign(p, q - p); p = q + 1; }
    gk.resize(NG); gout.resize(NG); glut.resize(NG); gins0.resize(NG + 1); ginit0.resize(NG + 1);
    for (int g = 0; g < NG; g++) {
        gorig.push_back(strtol(p, &e, 10)); p = e;    // original gate index (--gclass)
        gout[g] = strtol(p, &e, 10); p = e; gk[g] = strtol(p, &e, 10); p = e; glut[g] = strtol(p, &e, 10); p = e;
        bool isdsp = glut[g] == 2; if (isdsp) glut[g] = 0;   // a DSP48E1 output bit: no truth table, not a LUT
        bool isram = glut[g] == 3; if (isram) glut[g] = 0;   // a RAMB18E1 DOADO bit
        gdsp.push_back(-1); gram.push_back(-1);
        while (*p == ' ') p++;
        const char* h = p; while (isxdigit((unsigned char)*p)) p++;
        ginit0[g] = initw.size();
        int nw = (gk[g] <= 6 || isdsp || isram) ? 1 : (1 << (gk[g] - 6));
        vector<uint64_t> w(nw, 0);
        int nd = p - h;   // hex digits, least significant last
        for (int j = 0; j < nd; j++) {
            char c = h[nd - 1 - j]; uint64_t d = isdigit((unsigned char)c) ? c - '0' : (tolower(c) - 'a' + 10);
            int bit = 4 * j; if (bit / 64 >= nw) { if (d) die("init too wide"); continue; }
            w[bit / 64] |= d << (bit % 64);
        }
        for (auto x : w) initw.push_back(x);
        gins0[g] = ins.size();
        for (int i = 0; i < gk[g]; i++) { ins.push_back(strtol(p, &e, 10)); p = e; }
        for (int i = 0; i < gk[g]; i++) {
            afmin.push_back(strtoll(p, &e, 10)); p = e; afmax.push_back(strtoll(p, &e, 10)); p = e;
            asmin.push_back(strtoll(p, &e, 10)); p = e; asmax.push_back(strtoll(p, &e, 10)); p = e;
        }
        if (isdsp) {
            while (*p == ' ') p++; if (*p != 'D') die("bad dsp gate line"); p++;
            DspG d; d.obit = strtol(p, &e, 10); p = e; d.opm = strtol(p, &e, 10); p = e; d.alu = strtol(p, &e, 10); p = e;
            d.inm = strtol(p, &e, 10); p = e; d.cis = strtol(p, &e, 10); p = e; d.cin = strtol(p, &e, 10); p = e;
            for (int j = 0; j < 4; j++) { d.base[j] = strtoull(p, &e, 16); p = e; }
            for (int i = 0; i < gk[g]; i++) { d.roles.push_back(strtol(p, &e, 10)); p = e; }
            dsp48_p(d.opm, d.alu, d.inm, d.cis, 0, 0, 0, 0, d.cin);   // refuses an unmodelled configuration at load
            gdsp[g] = DSPG.size(); DSPG.push_back(d);
        }
        if (isram) {
            while (*p == ' ') p++; if (*p != 'R') die("bad ram gate line"); p++;
            RamG r; r.id = strtol(p, &e, 10); p = e; r.obit = strtol(p, &e, 10); p = e; r.base = strtoull(p, &e, 16); p = e;
            for (int j = 0; j < 3; j++) { r.su[j] = strtol(p, &e, 10); p = e; r.ho[j] = strtol(p, &e, 10); p = e; }
            for (int i = 0; i < gk[g]; i++) { r.roles.push_back(strtol(p, &e, 10)); p = e; }
            while (*p == ' ') p++; if (*p != 'M') die("bad ram gate line (M)"); p++;
            int nm = strtol(p, &e, 10); p = e;
            for (int j = 0; j < nm; j++) { int ad = strtol(p, &e, 10); p = e; unsigned w = strtoul(p, &e, 16); p = e; r.mem.push_back({ad, w}); }
            r.ini = (int)(initw[ginit0[g]] & 1);
            if ((int)RAMS.size() <= r.id) RAMS.resize(r.id + 1);
            RamS& st = RAMS[r.id];
            if (st.master < 0) { st.master = g; st.mem.assign(1024, 0); for (auto& m : r.mem) st.mem.at(m.first) = m.second; }
            gram[g] = RAMG.size(); RAMG.push_back(r);
        }
        while (*p == ' ') p++; if (*p != '\n') die("bad gate line"); p++;
    }
    gins0[NG] = ins.size(); ginit0[NG] = initw.size();
    for (int i = 0; i < 8; i++) {
        const char* q = strchr(p, ' '); string k(p, q - p); p = q; BN[k] = strtol(p, &e, 10); p = e + 1;
    }
    for (int j = 0; j < 3; j++) {
        const char* q = strchr(p, ' '); p = q; int n = strtol(p, &e, 10); p = e;
        for (int i = 0; i < n; i++) { Bdata[j].push_back(strtol(p, &e, 10)); p = e; }
        p++;
    }
    while (*p == '\n' || *p == ' ') p++;
    if (!strncmp(p, "xacks ", 6)) {   // margin/bram/mk_bnd_mem.py: the other input channels' acknowledges
        p += 6; int n = strtol(p, &e, 10); p = e;
        for (int i = 0; i < n; i++) { XACKS.push_back(strtol(p, &e, 10)); p = e; }
    }
    while (*p == '\n' || *p == ' ') p++;
    while (!strncmp(p, "xdata ", 6)) {   // xdata ack n node..  (margin/bram/mk_bnd_mem.py: a middle operand channel)
        p += 6; XData x; x.ack = strtol(p, &e, 10); p = e; int n = strtol(p, &e, 10); p = e;
        for (int i = 0; i < n; i++) { x.nodes.push_back(strtol(p, &e, 10)); p = e; }
        XDATA.push_back(x); while (*p == '\n' || *p == ' ') p++;
    }
    while (!strncmp(p, "host ", 5)) {   // host NAME req we ack na addr.. nw wdata..
        p += 5; const char* q = strchr(p, ' '); HostP h; h.name.assign(p, q - p); p = q;
        h.req = strtol(p, &e, 10); p = e; h.we = strtol(p, &e, 10); p = e; h.ack = strtol(p, &e, 10); p = e;
        int na = strtol(p, &e, 10); p = e; for (int i = 0; i < na; i++) { h.addr.push_back(strtol(p, &e, 10)); p = e; }
        int nw = strtol(p, &e, 10); p = e; for (int i = 0; i < nw; i++) { h.wdata.push_back(strtol(p, &e, 10)); p = e; }
        HOSTS.push_back(h); while (*p == '\n' || *p == ' ') p++;
    }
}

// ---------------- node histories: v0 and flip times (values alternate) ----------------
static vector<vector<int>> H;          // flip times after the initial entry at 0 (simadv's ts[1:])
static vector<char> V0, TOUCH;
static int LASTN = -1;                  // node of the most recent flip (--periodic)
static inline bool val(int n, ll t) {
    if (t < 0) return V0[n];
    const vector<int>& h = H[n];
    size_t c;
    if (h.empty() || h.back() <= t) c = h.size();
    else c = upper_bound(h.begin(), h.end(), (int)t) - h.begin();
    return V0[n] ^ (c & 1);
}
static inline bool cur(int n) { return V0[n] ^ (H[n].size() & 1); }
static bool setv(int n, ll t, bool v) {
    TOUCH[n] = 1;
    vector<int>& h = H[n];
    ll last = h.empty() ? 0 : h.back();
    if (last == t) {
        if (h.empty()) { if (V0[n] != v) { V0[n] = v; return true; } return false; }
        if (cur(n) == v) return false;
        h.pop_back(); return true;
    }
    if (t < last) { fprintf(stderr, "time went back on node %s\n", names[n].c_str()); exit(1); }
    if (cur(n) == v) return false;
    h.push_back((int)t); LASTN = n; return true;
}

// ---------------- event queue: (t, pri, seq, x) ----------------
struct Ev { ll t; int pri; ll seq; int x; };
struct EvCmp { bool operator()(const Ev& a, const Ev& b) const {
    if (a.t != b.t) return a.t > b.t; if (a.pri != b.pri) return a.pri > b.pri; return a.seq > b.seq; } };
// Same order as simadv's heap of (t, pri, seq): env/aux events (pri -1/-2, rare) in a heap; gate evaluations (pri 0)
// in a timing wheel of FIFO buckets (seq grows with insertion, so FIFO = seq order within a time; at equal t every
// pri < 0 event precedes every gate event, and nothing with pri < 0 is ever pushed at the current time).
struct EQ {
    priority_queue<Ev, vector<Ev>, EvCmp> env;
    vector<vector<int>> slot; vector<uint64_t> bits; size_t pos = 0; ll cnt = 0, base = 0, M = 0;
    void init(ll maxd) { ll h = 1024; while (h <= maxd + 1) h <<= 1; M = h - 1; slot.assign(h, {}); bits.assign(h / 64, 0); }
    inline void gate(ll t, int g) { ll i = t & M; slot[i].push_back(g); bits[i >> 6] |= 1ULL << (i & 63); cnt++; }
    inline ll wnext() {   // earliest wheel time >= base (cnt > 0)
        ll i0 = base & M; ll w = i0 >> 6; uint64_t m = bits[w] & (~0ULL << (i0 & 63));
        ll nw = (ll)bits.size();
        for (ll k = 0; k <= nw; k++) {
            if (m) { ll i = (w << 6) + __builtin_ctzll(m); return base + ((i - i0) & M); }
            w = (w + 1) % nw; m = bits[w];
        }
        die("wheel corrupt");
    }
    bool empty() const { return cnt == 0 && env.empty(); }
    inline ll top_t() { if (cnt == 0) return env.top().t; ll tw = wnext(); return (!env.empty() && env.top().t <= tw) ? env.top().t : tw; }
    inline Ev pop() {
        ll tw = cnt ? wnext() : 0;
        if (!env.empty() && (cnt == 0 || env.top().t <= tw)) { Ev e = env.top(); env.pop(); base = e.t; return e; }
        ll i = tw & M; vector<int>& v = slot[i]; int g = v[pos++]; cnt--;
        if (pos == v.size()) { v.clear(); pos = 0; bits[i >> 6] &= ~(1ULL << (i & 63)); }
        base = tw; return Ev{tw, 0, 0, g};
    }
};
static EQ Q;
static ll SEQ = 0;
static vector<int> rd0, rdg, rdd, rdf;   // readers CSR: node -> (gate, delay, delay after --tcut)
static ll TCUT = -1;                   // --tcut T: a slowed arc (class S) takes its F delay for input changes at or after T
static inline void sched(ll t, int g) { ++SEQ; Q.gate(t, g); }
static inline void env_set(ll t, int n, bool v) { Q.env.push({t, -1, ++SEQ, 2 * n + (v ? 1 : 0)}); }
static inline void changed(int n, ll t) {
    if (TCUT < 0 || t < TCUT) { for (int r = rd0[n]; r < rd0[n + 1]; r++) sched(t + rdd[r], rdg[r]); return; }
    // FIFO across the cut: a change at u >= T arrives at max(u + fast, T + slow), never before an earlier change
    for (int r = rd0[n]; r < rd0[n + 1]; r++) sched(max(t + rdf[r], TCUT + rdd[r]), rdg[r]);
}

// RAM: step every rising edge h of the clock node with h + d1 <= T (d1 = the master's sampling arc, role 1)
static void ram_step(int id, ll T) {
    RamS& st = RAMS[id]; int m = st.master; const RamG& r = RAMG[gram[m]]; int b0 = gins0[m], k = gk[m];
    int clk = -1, d1 = -1;
    for (int i = 0; i < k; i++) { if (r.roles[i] == 0) clk = ins[b0 + i]; if (r.roles[i] == 1) d1 = ds[b0 + i]; }
    const vector<int>& h = H[clk];
    while (st.ep < h.size()) {
        ll e = h[st.ep];
        if (e + d1 >= T) break;                     // strictly before T: every sampled value is final
        bool after = V0[clk] ^ ((st.ep + 1) & 1);
        st.ep++;
        if (!after) continue;                       // a falling edge: nothing
        ll sp = e + d1; ull v = r.base;
        for (int i = 0; i < k; i++) { int ro = r.roles[i]; if (ro < 2) continue;
            if (val(ins[b0 + i], sp - ds[b0 + i])) v |= 1ULL << ro; }
        bool w0 = (v >> 2) & 1, w1 = (v >> 3) & 1; int ad = (v >> 16) & 1023; unsigned di = (v >> 32) & 0xffff;
        unsigned& wd = st.mem[ad];
        if (w0) wd = (wd & 0xff00) | (di & 0xff);
        if (w1) wd = (wd & 0x00ff) | (di & 0xff00);
        st.outs.push_back({e, wd});                 // WRITE_FIRST: DO shows the word as it is after the write
        st.edges.push_back({sp, ad, w0 || w1});
    }
}
static ll RAMVIOL = 0; static string RAMVIOL_EX;
static ll RAMMIN[3][2]; static string RAMMIN_AT[3][2];   // smallest setup / hold margin (ps, after the window) per class ADDR / WE / DI
static void ram_checks() {   // setup / hold: no sampled pin changes within [sp - SETUP, sp + HOLD] of its own sample point
    for (int c = 0; c < 3; c++) for (int j = 0; j < 2; j++) RAMMIN[c][j] = 1LL << 50;
    for (size_t id = 0; id < RAMS.size(); id++) {
        RamS& st = RAMS[id]; if (st.master < 0) continue;
        int m = st.master; const RamG& r = RAMG[gram[m]]; int b0 = gins0[m], k = gk[m];
        for (auto& ed : st.edges) {
            ll s = get<0>(ed); bool wrote = get<2>(ed);
            for (int i = 0; i < k; i++) { int ro = r.roles[i]; if (ro < 2) continue;
                int cls = ro < 16 ? 1 : ro < 32 ? 0 : 2;   // 0 ADDR, 1 WE, 2 DI
                if (cls == 2 && !wrote) continue;
                ll sp = s - ds[b0 + i]; const vector<int>& h = H[ins[b0 + i]];
                {   // margins: last change at or before sp (setup), first change after sp (hold)
                    auto u = upper_bound(h.begin(), h.end(), (int)sp);
                    if (u != h.begin()) { ll m_ = sp - *(u - 1) - r.su[cls];
                        if (m_ < RAMMIN[cls][0]) { RAMMIN[cls][0] = m_; char b[300]; snprintf(b, sizeof b, "ram %zu pin %s at %lld", id, names[ins[b0 + i]].c_str(), sp); RAMMIN_AT[cls][0] = b; } }
                    if (u != h.end()) { ll m_ = *u - sp - r.ho[cls];
                        if (m_ < RAMMIN[cls][1]) { RAMMIN[cls][1] = m_; char b[300]; snprintf(b, sizeof b, "ram %zu pin %s at %lld", id, names[ins[b0 + i]].c_str(), sp); RAMMIN_AT[cls][1] = b; } }
                }
                auto it = upper_bound(h.begin(), h.end(), (int)(sp - r.su[cls]));
                if (it != h.end() && *it <= sp + r.ho[cls]) {
                    RAMVIOL++;
                    if (RAMVIOL <= 3) { char b[400]; snprintf(b, sizeof b, "%s(ram %zu %s pin %s sampled at %lld ps, changed at %d ps)",
                        RAMVIOL > 1 ? ", " : "", id, names[gout[m]].c_str(), names[ins[b0 + i]].c_str(), sp, *it); RAMVIOL_EX += b; }
                }
            }
        }
    }
}
static int W = 0; static ll NSKIP = 0;
// RACES=1 (env): closest input reorderings at storage LUTs (class 0) and at LUTs feeding one (class 1), after reset
static bool RACEON = false; static ll RACEX = 300, RACET0 = 5000; static vector<char> RACEG;   // RACES_T0: skip this long after reset release (start-up settling)
struct RaceRec { ll gap; int g, q; ll t; };
static vector<RaceRec> RACEB[2]; static ll RACEN[2] = {0, 0}; static map<pair<int, int>, ll> RACEMIN[2];
static void race_note(int c, ll gap, int g, int q, ll t) {
    RACEN[c]++;
    auto key = make_pair(g, q); auto it = RACEMIN[c].find(key);
    if (it == RACEMIN[c].end() || gap < it->second) { RACEMIN[c][key] = gap; RACEB[c].push_back({gap, g, q, t}); }
}
static ll NINJ = 0;
static ll PER_L = 0; static vector<int> PER_B; static bool PER_HIT = false;
static map<pair<int, int>, ll> INF;
static inline bool fval(int n, ll r, ll& u) {
    if (r < 0) { u = r; return V0[n]; }
    const vector<int>& h = H[n];
    // ts = [0] + h; k = bisect_right(ts, r) - 1 = number of h entries <= r
    ll k = upper_bound(h.begin(), h.end(), (int)r) - h.begin();
    u = r;
    ll len = (ll)h.size() + 1;
    auto TS = [&](ll i) -> ll { return i == 0 ? 0 : h[i - 1]; };
    while (k + 1 < len && TS(k + 1) - TS(k) < W && TS(k + 1) <= r + W) {
        if (k == 0) break;
        u = TS(k) - 1; k--; NSKIP++;
    }
    return V0[n] ^ (k & 1);
}

static string pylist(const vector<ull>& v) {
    string s = "["; char b[32];
    for (size_t i = 0; i < v.size(); i++) { snprintf(b, sizeof b, "%s%llu", i ? ", " : "", v[i]); s += b; }
    return s + "]";
}

static const char* GCLF = nullptr; static double DBC = -1, DBR = -1, DBX = -1;
static bool DRAWON = false; static ll DRAW = 0; static double DBAND = 0.38, DSREG = 0.16, DSARC = 0.126; static int DREGSZ = 10;
static ull mix64(ull z) { z += 0x9E3779B97F4A7C15ULL; z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; return z ^ (z >> 31); }
static double hash_n(ll seed, ull tag, ull a, ull b) {   // a standard normal from (seed, tag, a, b): Box-Muller on two hashes
    ull h1 = mix64(mix64(mix64((ull)seed ^ tag) ^ a) ^ b), h2 = mix64(h1 ^ 0xD1B54A32D192ED03ULL);
    double u1 = ((h1 >> 11) + 1.0) / 9007199254740993.0, u2 = (h2 >> 11) / 9007199254740992.0;
    return sqrt(-2 * log(u1)) * cos(2 * M_PI * u2);
}
static double region_n(const string& nm) {   // the region of a SLICE_XxYy node name; 0 (factor 1) if none
    size_t p = nm.find("SLICE_X"); if (p == string::npos) return 0;
    int x = 0, y = 0; if (sscanf(nm.c_str() + p, "SLICE_X%dY%d", &x, &y) != 2) return 0;
    return hash_n(DRAW, 0x7E6105ULL, (ull)(x / DREGSZ), (ull)(y / DREGSZ));
}
int main(int argc, char** argv) {
    if (argc == 2 && !strcmp(argv[1], "--dsptest")) {   // stdin "opm alu inm cis A B C PCIN cin" (hex values) -> P (hex)
        int o, al, im, cs, ci; ull A, B, C, PC;
        while (scanf("%d %d %d %d %llx %llx %llx %llx %d", &o, &al, &im, &cs, &A, &B, &C, &PC, &ci) == 9) printf("%llx\n", dsp48_p(o, al, im, cs, A, B, C, PC, ci));
        return 0;
    }
    if (argc < 2) die("usage: simx NET.simx --pairs a,b ... [simadv options]");
    const char* netf = argv[1];
    vector<pair<ull, ull>> pairs; vector<vector<ull>> pairsx; vector<string> pairstr; vector<ull> wantv; bool has_want = false; string kernel = "gcd";
    double corner = 0.5, kappa = NAN; const char* classes = nullptr; char cdefault = 'M';
    bool data0 = false, full = false, pipelined = false; ll R = 20000, su = 0, dout = 3000, dfall = -1, tmax = 5000000, reqgap = 0, maxev = -1, hostd = 1;
    string datachange = "handshake", nextreq = "sample"; const char* dump = nullptr; bool periodic = false; const char* memf = nullptr; bool hostport = false;
    for (int i = 2; i < argc; i++) {
        string o = argv[i];
        auto nxt = [&]() -> const char* { if (i + 1 >= argc) die("missing value for %s", o.c_str()); return argv[++i]; };
        if (o == "--pairs") { while (i + 1 < argc && strncmp(argv[i + 1], "--", 2)) { string s = argv[++i]; size_t c = s.find(',');
                if (c == string::npos) die("bad pair %s", s.c_str());
                pairstr.push_back(s);
                size_t c2 = s.rfind(',');   // a,m1,..,b: the middle values go to the xdata channels in order
                vector<ull> mid; size_t q0 = c + 1;
                while (q0 < c2) { size_t q1 = s.find(',', q0); mid.push_back(strtoull(s.substr(q0, q1 - q0).c_str(), nullptr, 0)); q0 = q1 + 1; }
                pairsx.push_back(mid);
                pairs.push_back({strtoull(s.substr(0, c).c_str(), nullptr, 0), strtoull(s.substr(c2 + 1).c_str(), nullptr, 0)}); } }
        else if (o == "--kernel") kernel = nxt();
        else if (o == "--want") { has_want = true; string s = nxt(); size_t q = 0;   // expected out0 list (replaces gcd)
            while (q < s.size()) { size_t c = s.find(',', q); if (c == string::npos) c = s.size(); if (c > q) wantv.push_back(strtoull(s.substr(q, c - q).c_str(), nullptr, 0)); q = c + 1; } }
        else if (o == "--corner") corner = atof(nxt());
        else if (o == "--kappa") kappa = atof(nxt());
        else if (o == "--classes") classes = nxt();
        else if (o == "--cdefault") { const char* c = nxt(); cdefault = c[0]; if (strlen(c) != 1 || !strchr("SFM", c[0])) die("bad --cdefault"); }
        else if (o == "--data0") data0 = true;
        else if (o == "--full") full = true;
        else if (o == "--pipelined") pipelined = true;
        else if (o == "--R") R = atoll(nxt());
        else if (o == "--su") su = atoll(nxt());
        else if (o == "--dout") dout = atoll(nxt());
        else if (o == "--dfall") dfall = atoll(nxt());
        else if (o == "--tmax") tmax = atoll(nxt());
        else if (o == "--reqgap") reqgap = atoll(nxt());
        else if (o == "--hostdelay") { hostd = atoll(nxt()); if (hostd < 1) hostd = 1; }   // the host moves input data >= this many ps after the acknowledge it reacts to (Spec.Env allows any delay >= 0; default 1 = the most adversarial host)
        else if (o == "--w") W = atoi(nxt());
        else if (o == "--maxev") maxev = atoll(nxt());
        else if (o == "--datachange") { datachange = nxt(); if (datachange != "handshake" && datachange != "broad" && datachange != "rtz" && datachange != "next") die("bad --datachange"); }
        else if (o == "--nextreq") { nextreq = nxt(); if (nextreq != "sample" && nextreq != "seq") die("bad --nextreq"); }
        else if (o == "--dump") dump = nxt();
        else if (o == "--tcut") TCUT = atoll(nxt());
        else if (o == "--periodic") periodic = true;
        else if (o == "--draw") { DRAW = atoll(nxt()); DRAWON = true; }        // random delay draw (board approximator), seed
        else if (o == "--band") DBAND = atof(nxt());
        else if (o == "--sreg") DSREG = atof(nxt());
        else if (o == "--sarc") DSARC = atof(nxt());
        else if (o == "--regsize") DREGSZ = atoi(nxt());
        else if (o == "--gclass") GCLF = nxt();          // research's draw model: per-gate class file "gi c|r|x|q|p"
        else if (o == "--bands") { if (sscanf(nxt(), "%lf,%lf,%lf", &DBC, &DBR, &DBX) != 3) die("--bands bc,br,bx"); }   // stop with PERIODIC when the run provably (untrusted) repeats
        else if (o == "--mem") memf = nxt();
        else if (o == "--hostport") hostport = true;   // fills go through each array's host port (the bench's sequencer), not into the RAM   // RAM contents: "F k id addr hex" fill before call k, "X k id addr hex" expected after call k
        else if (o == "--pos" || o == "--seed") nxt();
        else die("unsupported option %s (simx ports only simadv's --classes/--full subset)", o.c_str());
    }
    if (dfall < 0) dfall = dout;
    if (kernel != "gcd" && !has_want) die("--kernel %s: pass the expected out0 list with --want (margin.py does, from kernels.py)", kernel.c_str());
    if (!full) die("only --full is ported");
    if (DRAWON) { if (std::isnan(kappa)) kappa = 0; if (!classes) classes = "/dev/null"; }
    if (!classes || std::isnan(kappa)) die("only --classes with --kappa is ported");
    if (tmax > 2000000000LL) die("--tmax too large (int32 histories)");
    const char* kd = getenv("KDEN"); ll KD = kd ? atoll(kd) : 25; ll PK = (ll)nearbyint(kappa * KD);
    if (!(corner == 0 || corner == 1) || !(fabs(kappa - (double)PK / KD) < 1e-12)) die("kappa must be P/KDEN exactly, corner 0 or 1");
    bool slowc = corner == 1;

    load_net(netf);
    map<ll, vector<tuple<int, int, unsigned>>> MFILL, MEXP; ll memmis = 0, memchk = 0; string memex;
    map<ll, vector<tuple<int, int, unsigned>>> HFILL;   // call -> (host index, element index, word): --hostport
    if (memf) { FILE* f = fopen(memf, "r"); if (!f) die("cannot open %s", memf); char line[512];
        while (fgets(line, sizeof line, f)) {
            char c, nm[200]; ll kk; int id, ad; unsigned w;
            if (line[0] == 'H') {
                if (sscanf(line, "H %lld %199s %d %x", &kk, nm, &ad, &w) != 4) die("--mem: bad H line");
                int hi = -1; for (size_t j = 0; j < HOSTS.size(); j++) if (HOSTS[j].name == nm) hi = j;
                if (hi < 0) { if (hostport) die("--mem: no host port %s", nm); continue; }
                HFILL[kk].push_back({hi, ad, w}); continue; }
            if (sscanf(line, " %c %lld %d %d %x", &c, &kk, &id, &ad, &w) != 5) continue;
            if (id < 0 || id >= (int)RAMS.size() || RAMS[id].master < 0 || ad < 0 || ad >= 1024) die("--mem: bad ram id / address");
            (c == 'F' ? MFILL : MEXP)[kk].push_back({id, ad, w}); }
        fclose(f); fprintf(stderr, "simx: --mem %zu fill calls, %zu checked calls, %zu RAMs, %zu host ports%s\n", MFILL.size(), MEXP.size(),
                           RAMS.size(), HOSTS.size(), hostport ? " (fills THROUGH the host ports)" : ""); }
    auto mem_check = [&](ll kc, ll tt) {
        for (size_t id = 0; id < RAMS.size(); id++) if (RAMS[id].master >= 0) ram_step(id, tt);
        auto it = MEXP.find(kc); if (it == MEXP.end()) return;
        for (auto& x : it->second) { memchk++; unsigned got = RAMS[get<0>(x)].mem[get<1>(x)];
            if (got != get<2>(x)) { memmis++; if (memmis <= 3) { char b[200]; snprintf(b, sizeof b, "%s(call %lld ram %d word %d: %04x, want %04x)", memmis > 1 ? ", " : "", kc, get<0>(x), get<1>(x), got, get<2>(x)); memex += b; } } }
    };
    auto mem_fill = [&](ll kc, ll tt) {
        for (size_t id = 0; id < RAMS.size(); id++) if (RAMS[id].master >= 0) ram_step(id, tt);
        auto it = MFILL.find(kc); if (it == MFILL.end()) return;
        for (auto& x : it->second) RAMS[get<0>(x)].mem[get<1>(x)] = get<2>(x);
    };
    vector<char> GCL(NG, 'r');
    if (GCLF) { map<int, char> m; FILE* f = fopen(GCLF, "r"); if (!f) die("cannot open %s", GCLF); int gi; char c;
      while (fscanf(f, "%d %c", &gi, &c) == 2) m[gi] = c; fclose(f);
      size_t hit = 0; for (int g = 0; g < NG; g++) { auto it = m.find(gorig[g]); if (it != m.end()) { GCL[g] = it->second; hit++; } }
      if (DBC < 0) die("--gclass needs --bands");
      fprintf(stderr, "simx: --gclass %zu of %d gates classed\n", hit, NG); }
    fprintf(stderr, "sim: cone %d gates of %d (%d nodes)\n", NG, NGALL, NSEEN);

    // classes: node name -> class, (node name, pin) -> class; F first then S (S wins), as simadv
    map<string, char> CLSn; map<pair<string, int>, char> ACLn; map<pair<string, int>, ll> INJn;
    if (strcmp(classes, "/dev/null")) { string s = slurp(classes); JP jp{s.c_str()}; JV j = jp.val(); if (j.ty != 4) die("classes: not an object");
      for (char kc : {'F', 'S'}) for (auto& kv : j.o) if (kv.first.size() == 1 && kv.first[0] == kc) for (auto& x : kv.second.a) {
          if (x.ty == 3) ACLn[{x.a.at(0).s, (int)x.a.at(1).num}] = kc; else CLSn[x.s] = kc; }
      // "I": [[node, pin, ps], ...]: an EXTRA delay added to that arc (an injection OUTSIDE the prjxray band, for negative
      // controls such as research's SDF injections; a run with injections is not a Spec behaviour)
      for (auto& kv : j.o) if (kv.first == "I") for (auto& x : kv.second.a) INJn[{x.a.at(0).s, (int)x.a.at(1).num}] = (ll)x.a.at(2).num; }
    vector<char> CLS(NN, 0); map<pair<int, int>, char> ACL; map<pair<int, int>, ll> INJ;
    { size_t found = 0; map<string, int> want; for (auto& kv : CLSn) want[kv.first] = 1; for (auto& kv : ACLn) want[kv.first.first] = 1;
      map<string, int> nid;
      for (int i = 0; i < NN; i++) { auto it = want.find(names[i]); if (it != want.end()) { nid[names[i]] = i; found++; } }
      for (auto& kv : want) if (!nid.count(kv.first)) die("classes: unknown node %s", kv.first.c_str());
      for (auto& kv : CLSn) CLS[nid[kv.first]] = kv.second;
      for (auto& kv : ACLn) ACL[{nid[kv.first.first], kv.first.second}] = kv.second;
      for (auto& kv : INJn) { auto it = nid.find(kv.first.first); if (it == nid.end()) { for (int i = 0; i < NN; i++) if (names[i] == kv.first.first) { nid[names[i]] = i; break; } }
        if (!nid.count(kv.first.first)) die("classes: unknown injected node %s", kv.first.first.c_str());
        INJ[{nid[kv.first.first], kv.first.second}] = kv.second; } }

    ds.resize(ins.size()); his.assign(ins.size(), 0.0); vector<int> dsf(ins.size());
    for (int g = 0; g < NG; g++) {
        for (int i = 0; i < gk[g]; i++) {
            int a = gins0[g] + i;
            char k = CLS[gout[g]] ? CLS[gout[g]] : cdefault;
            auto it = ACL.find({gout[g], i}); if (it != ACL.end()) k = it->second;
            ll FX = slowc ? asmax[a] : afmax[a], FN = slowc ? asmin[a] : afmin[a];
            ll d;
            if (k == 'S') d = ((KD + PK) * FX) / KD;
            else if (k == 'F') d = ((KD - PK) * FN + KD - 1) / KD;
            else d = (FN + FX) / 2;
            if (FX < 0 || FN < 0) die("negative arc delay");
            if (W && glut[g]) {
                his[a] = ((1 - corner) * (double)afmax[a] + corner * (double)asmax[a]) * (1 + kappa) * 1.0;
                if (d < W) { if (!(W <= his[a])) die("H_RUNT: w exceeds a LUT pin's upper bound"); d = W; }
            }
            ll df = d;
            if (k == 'S') { df = ((KD - PK) * FN + KD - 1) / KD; if (W && glut[g] && df < W) df = W; }
            if (DRAWON) {   // board approximator: band position, lognormal region and per-arc factors (no adversary)
                double band = DBAND, f;
                if (GCLF) {   // research's model (FOR-FORMAL 2026-11-16): band per class; pips: per-pip scatter; all: region
                    char c = GCL[g]; band = (c == 'c' || c == 'q') ? DBC : c == 'x' ? DBX : DBR;
                    f = exp(DSREG * region_n(names[gout[g]]) + ((c == 'p' || c == 'q') ? DSARC * hash_n(DRAW, 0x51ED2701ULL, (ull)gout[g], (ull)i) : 0.0));
                } else
                    f = exp(DSREG * region_n(names[gout[g]]) + DSARC * hash_n(DRAW, 0x51ED2701ULL, (ull)gout[g], (ull)i));
                double base = (double)afmin[a] + band * ((double)asmax[a] - (double)afmin[a]);
                d = (ll)llround(base * f); if (d < 1) d = 1;
                if (W && glut[g]) { if (d < W) d = W; his[a] = (double)d; }
                df = d;
            }
            { auto ij = INJ.find({gout[g], i}); if (ij != INJ.end()) { d += ij->second; df += ij->second; NINJ++; if (d < 1) d = 1; if (df < 1) df = 1; } }   // clamp: a negative injection never makes an arc negative (2026-11-18)
            ds[a] = (int)d; dsf[a] = (int)df;
        }
    }
    if (NINJ) fprintf(stderr, "simx: %lld injected arcs (outside the prjxray band: NOT a Spec behaviour)\n", NINJ);
    // readers CSR (simadv: readers[n].append in cone order, pin order)
    rd0.assign(NN + 1, 0);
    for (int g = 0; g < NG; g++) for (int i = 0; i < gk[g]; i++) rd0[ins[gins0[g] + i] + 1]++;
    for (int n = 0; n < NN; n++) rd0[n + 1] += rd0[n];
    rdg.resize(ins.size()); rdd.resize(ins.size()); rdf.resize(ins.size());
    { vector<int> f(rd0.begin(), rd0.end() - 1);
      for (int g = 0; g < NG; g++) for (int i = 0; i < gk[g]; i++) { int n = ins[gins0[g] + i]; rdg[f[n]] = g; rdd[f[n]] = ds[gins0[g] + i]; rdf[f[n]] = dsf[gins0[g] + i]; f[n]++; } }
    H.assign(NN, {}); V0.assign(NN, 0); TOUCH.assign(NN, 0);
    if (getenv("RACES") && atoi(getenv("RACES"))) {
        RACEON = true; if (getenv("RACES_PS")) RACEX = atoll(getenv("RACES_PS")); if (getenv("RACES_T0")) RACET0 = atoll(getenv("RACES_T0"));
        RACEG.assign(NG, 0);
        vector<int> drv0(NN, -1); for (int g = 0; g < NG; g++) drv0[gout[g]] = g;
        // a decoded LUT reads its own output through a copy chain (pips / hops: k = 1, INIT 2), as races.py's chain()
        auto src = [&](int u) { for (int d = 0; d < 200; d++) { int h = drv0[u]; if (h < 0 || glut[h] || gk[h] != 1 || initw[ginit0[h]] != 2) break; u = ins[gins0[h]]; } return u; };
        for (int g = 0; g < NG; g++) if (glut[g]) for (int i = gins0[g]; i < gins0[g + 1]; i++) if (src(ins[i]) == gout[g]) { RACEG[g] = 1; break; }
        // class 1: LUTs whose output a storage LUT reads (directly or through pips / hops only)
        vector<char> feeds(NN, 0);
        for (int g = 0; g < NG; g++) if (RACEG[g] == 1) for (int i = gins0[g]; i < gins0[g + 1]; i++) if (ins[i] != gout[g]) feeds[ins[i]] = 1;
        for (int it = 0; it < 400; it++) { bool ch = false;   // walk back through non-LUT single-input gates (pips, hops)
            for (int g = 0; g < NG; g++) if (!glut[g] && feeds[gout[g]] && gk[g] == 1 && initw[ginit0[g]] == 2 && !feeds[ins[gins0[g]]]) { feeds[ins[gins0[g]]] = 1; ch = true; }
            if (!ch) break; }
        for (int g = 0; g < NG; g++) if (glut[g] && !RACEG[g] && feeds[gout[g]]) RACEG[g] = 2;
    }

    int rst = BN["rst"], req = BN["req"], aA = BN["a_ack"], aB = BN["b_ack"], aS = BN["start_ack"],
        oR = BN["out0_req"], oA = BN["out0_ack"], eA = BN["pend_ack"];
    for (int n : Bdata[2]) if (n < 0) die("const bit in out0_data");
    auto drive_data = [&](ll t, ull vals, int key) {
        vector<pair<int, bool>> want;  // insertion-ordered dict
        const char* kn = key == 0 ? "a_data" : "b_data";
        for (size_t i = 0; i < Bdata[key].size(); i++) {
            bool bit = i < 64 ? (vals >> i) & 1 : 0; int n = Bdata[key][i];
            if (n < 0) { if (bit != (n == -2)) { fprintf(stderr, "pair value %#llx not representable on %s: bit %zu tied to %s\n", vals, kn, i, n == -2 ? "const1" : "const0"); exit(1); } continue; }
            bool f = false;
            for (auto& x : want) if (x.first == n) { f = true; if (x.second != bit) { fprintf(stderr, "pair value %#llx not representable on %s: bit %zu shares a node\n", vals, kn, i); exit(1); } }
            if (!f) want.push_back({n, bit});
        }
        for (auto& x : want) env_set(t, x.first, x.second);
    };
    { ll md = 0; for (int x : ds) md = max(md, (ll)x); double hm = 0; for (double x : his) hm = max(hm, x);
      PER_L = md + (W ? (ll)ceil(hm) + W : 0) + 2; PER_B = {rst, req, aA, aB, aS, oR, oA}; if (eA >= 0) PER_B.push_back(eA); for (int x : XACKS) PER_B.push_back(x); }
    env_set(0, rst, true);
    env_set(R, rst, false);
    { ll md = 0; for (int x : ds) md = max(md, (ll)x); Q.init(md); }
    for (int g = 0; g < NG; g++) sched(0, g);
    // env state
    ll data_at = 0;
    ll k = 0, done_in = 0; bool out_pending = false, next_ok = true, seq_wait = false;
    bool has_sample = false; ll sample_at = 0; ll broad_k[2] = {-1, -1}; ll rtz_done = -1;
    ll np = pairs.size();
    auto drive_x = [&](ll tt, ll kk, int only) {   // the middle operand channels (XDATA) of pair kk; only = one channel or -1
        if (pairsx[kk].size() != XDATA.size()) { fprintf(stderr, "pair %lld has %zu middle values, the boundary %zu middle channels\n", kk, pairsx[kk].size(), XDATA.size()); exit(1); }
        for (size_t c = 0; c < XDATA.size(); c++) { if (only >= 0 && (int)c != only) continue;
            for (size_t i = 0; i < XDATA[c].nodes.size(); i++) { int n = XDATA[c].nodes[i]; if (n < 0) continue;
                env_set(tt, n, i < 64 ? (pairsx[kk][c] >> i) & 1 : 0); } }
    };
    vector<ll> broad_x(XDATA.size(), -1);
    if (np) { ll t0d = data0 ? 0 : (su ? R - su - 1 : R); drive_data(t0d, pairs[0].first, 0); drive_data(t0d, pairs[0].second, 1); drive_x(t0d, 0, -1); }
    ll t = 0, nev = 0; vector<pair<ll, ull>> outvals;
    int hst = 0; ll hk = -1, hq = 0, hnext = 0, hgap = 0, nhost = 0;
    const ll HCLK = getenv("HOSTCLK") ? atoll(getenv("HOSTCLK")) : 12000, HGAP = getenv("HOSTGAP") ? atoll(getenv("HOSTGAP")) : 8;
    bool req_state = false, pend_state = false, capped = false;
    const int* INS = ins.data(); const int* DS = ds.data(); const int* DSF = dsf.data();
    if (TCUT >= 0) fprintf(stderr, "simx: --tcut %lld: slowed arcs take their F delay for input changes at or after it\n", TCUT);
    // the pin's sample point: slow while t < T + slow (changes before T), fast after (inverse of the FIFO arrival map)
    auto PD = [&](int a, ll tt) -> ll { return (TCUT < 0 || tt < TCUT + DS[a]) ? DS[a] : DSF[a]; };
    while (!Q.empty()) {
        Ev e = Q.pop();
        t = e.t;
        if (t > tmax) break;
        if (maxev >= 0 && nev >= maxev) { capped = true; break; }
        nev++;
        if (e.pri == -1) { int n = e.x >> 1; if (setv(n, t, e.x & 1)) changed(n, t); }
        else if (e.pri == -2) {}
        else {
            int g = e.x, kk = gk[g], b0 = gins0[g]; unsigned ad = 0;
            if (W && glut[g]) {
                for (int i = 0; i < kk; i++) { ll u; bool v = fval(INS[b0 + i], t - PD(b0 + i, t), u);
                    if ((double)(t - u) > his[b0 + i]) INF[{g, i}]++;
                    if (v) ad |= 1u << i; }
            } else if (gdsp[g] < 0 && gram[g] < 0) for (int i = 0; i < kk; i++) if (val(INS[b0 + i], t - PD(b0 + i, t))) ad |= 1u << i;
            bool v;
            if (gram[g] >= 0) {   // RAMB18E1 DOADO bit: the word of the last edge whose DO arc (role 0) has elapsed
                const RamG& r = RAMG[gram[g]]; ram_step(r.id, t);
                int d0 = 0; for (int i = 0; i < kk; i++) if (r.roles[i] == 0) d0 = DS[b0 + i];
                const auto& o = RAMS[r.id].outs;
                auto it = upper_bound(o.begin(), o.end(), make_pair(t - d0, (unsigned)0xffffffffu));
                v = it == o.begin() ? r.ini : (((it - 1)->second >> r.obit) & 1);
            } else if (gdsp[g] >= 0) {   // DSP48E1 output bit: every data pin read at t - its arc (transport), the datapath, bit obit
                const DspG& d = DSPG[gdsp[g]]; ull pv[4] = {d.base[0], d.base[1], d.base[2], d.base[3]};
                for (int i = 0; i < kk; i++) if (val(INS[b0 + i], t - PD(b0 + i, t))) pv[d.roles[i] >> 6] |= 1ULL << (d.roles[i] & 63);
                v = (dsp48_p(d.opm, d.alu, d.inm, d.cis, pv[0], pv[1], pv[2], pv[3], d.cin) >> d.obit) & 1;
            } else v = (initw[ginit0[g] + (ad >> 6)] >> (ad & 63)) & 1;
            if (RACEON && t >= R + RACET0 && RACEG[g]) {
                // RACES (informational; rewritten 2026-11-17 06:1x): a LUT's SENSITIVITY window on a pin. With ad the inputs
                // read now and ap the inputs read just before (each pin at its sample point - 1 ps), pin q is "open" when
                // flipping q changes the output.
                //  setup: q was open before and is closed now (another pin's arrival at t closed it), q not arriving at t:
                //         gap = t - q's last arrival (data settled gap ps before the window closed);
                //  hold:  q arrives at t and is closed now, and was open with some pin p at its value before p's last
                //         arrival: gap = t - p's arrival (data moved gap ps after the window closed).
                // A reordering within gap ps flips what this LUT stores or passes. gap 0 is skipped.
                auto F = [&](unsigned x) -> bool { return (initw[ginit0[g] + (x >> 6)] >> (x & 63)) & 1; };
                unsigned ap = 0; ll arr[8]; bool now[8];
                for (int q = 0; q < kk; q++) {
                    ll sp = t - PD(b0 + q, t); const vector<int>& h = H[INS[b0 + q]];
                    ll idx = (ll)(upper_bound(h.begin(), h.end(), (int)sp) - h.begin()) - 1;
                    arr[q] = idx < 0 ? -1 : t - (sp - h[idx]); now[q] = arr[q] == t;
                    if (val(INS[b0 + q], sp - 1)) ap |= 1u << q;
                }
                for (int q = 0; q < kk; q++) {
                    bool openNow = F(ad) != F(ad ^ (1u << q));
                    if (openNow) continue;
                    if (!now[q]) {
                        bool openPrev = F(ap) != F(ap ^ (1u << q));
                        if (openPrev && arr[q] >= 0 && t - arr[q] < RACEX) race_note(RACEG[g] - 1, t - arr[q], g, q, t);
                    } else {
                        ll best = -1; int bp = -1;
                        for (int p2 = 0; p2 < kk; p2++) if (p2 != q && !now[p2] && arr[p2] >= 0 && t - arr[p2] < RACEX) {
                            unsigned x = ad ^ (1u << p2); if (F(x) != F(x ^ (1u << q)) && (best < 0 || t - arr[p2] < best)) { best = t - arr[p2]; bp = p2; }
                        }
                        if (best > 0) race_note(RACEG[g] - 1, best, g, bp, t);   // reported at the closing pin bp
                    }
                }
            }
            if (setv(gout[g], t, v)) changed(gout[g], t);
        }
        if (periodic && t > R && (nev & ((1 << 18) - 1)) == 0 && Q.env.empty() && LASTN >= 0 && hst == 0) {   // hst: the host's sequencer is a clock, not an idle env
            // Eventual periodicity (UNTRUSTED argument, as Lean's Frontier36 made by hand): every gate reads its inputs at
            // most maxD + lookback ps back, so if every node's history on (te-L, te] equals its history on (te-L-P, te-P]
            // shifted by P (values at the window starts included), no boundary node moved in (te-L-P, te] and the env has
            // nothing pending, the run from te-P repeats with period P for ever (the env is idle: it reacts only to
            // boundary changes). te = t-1: every event before t is processed.
            ll te = t - 1, L = PER_L;
            const vector<int>& hr = H[LASTN];
            int nc = 0;
            for (ll j = (ll)hr.size() - 2; j >= 0 && nc < 8; j--) {
                ll P = (ll)hr.back() - hr[j]; if (P <= 0) continue; if (P > 50000) break;
                if (hr.back() > te) continue;
                nc++;
                bool okp = te - L - P > R;
                for (int bn : PER_B) if (okp) { const vector<int>& hb = H[bn]; if (!hb.empty() && hb.back() > te - L - P) okp = false; }
                for (int n = 0; n < NN && okp; n++) {
                    const vector<int>& h = H[n];
                    if (val(n, te - L) != val(n, te - L - P)) { okp = false; break; }
                    if (h.empty() || h.back() <= te - L - P) continue;
                    auto a0 = upper_bound(h.begin(), h.end(), (int)(te - L)), a1 = upper_bound(h.begin(), h.end(), (int)te);
                    auto b0 = upper_bound(h.begin(), h.end(), (int)(te - L - P)), b1 = upper_bound(h.begin(), h.end(), (int)(te - P));
                    if (a1 - a0 != b1 - b0) { okp = false; break; }
                    for (auto x = a0, y = b0; x != a1; ++x, ++y) if (*x != *y + P) { okp = false; break; }
                }
                if (okp) {
                    fprintf(stderr, "simx: PERIODIC: the run repeats with period %lld ps from %lld ps (checked window %lld ps at %lld ps; boundary idle)\n", P, te - L - P, L, te);
                    PER_HIT = true; break;
                }
            }
            if (PER_HIT) { t = t - 1; break; }   // the dump ends at te: every event before t is processed
        }
        if (!Q.empty() && Q.top_t() == t) continue;
        if (t < R) continue;
        // ---- the environment reacts to the settled state at t
        bool A0 = val(aA, t), A1 = val(aB, t), A2 = val(aS, t); TOUCH[aA] = TOUCH[aB] = TOUCH[aS] = 1;
        bool anyA = A0 || A1 || A2, allA = A0 && A1 && A2;
        for (int x : XACKS) { bool v = val(x, t); TOUCH[x] = 1; anyA = anyA || v; allA = allA && v; }
        if (datachange == "broad" && 0 < k && k < np) {
            int ackn[2] = {aA, aB};
            for (int j = 0; j < 2; j++) if (!val(ackn[j], t) && broad_k[j] != k) {
                broad_k[j] = k;
                printf("env: %s -> pair %lld at %lld ps (its ack fell)\n", j ? "b_data" : "a_data", k, t + 1);
                drive_data(t + hostd, j ? pairs[k].second : pairs[k].first, j);
                data_at = max(data_at, t + hostd);
            }
            for (size_t c = 0; c < XDATA.size(); c++) if (!val(XDATA[c].ack, t) && broad_x[c] != k) {
                broad_x[c] = k; drive_x(t + hostd, k, (int)c); data_at = max(data_at, t + hostd); }
        }
        if (datachange == "rtz" && !req_state && !anyA && 0 < k && k < np && rtz_done != k) {
            rtz_done = k;
            printf("env: data -> pair %lld at %lld ps (all acks low, before out0)\n", k, t + 1);
            drive_data(t + hostd, pairs[k].first, 0); drive_data(t + hostd, pairs[k].second, 1); drive_x(t + hostd, k, -1);
        }
        // --hostport: before call k the bench's sequencer (gen_bench.py) writes call k's arrays through the host ports, one
        // element at a time, on aclk (HOSTCLK ps) edges: payload (addr, data, we) at a start edge, the request at the next edge
        // once the synchronised acknowledge is low, the request dropped at the edge that sees it high, done at the edge that
        // sees it low again; the acknowledge as seen at edge e is its value at e - 2 HOSTCLK (2-flop synchroniser); HOSTGAP
        // idle edges between accesses (the PS's AXI writes).
        if (hostport && hst == 0 && hk != k && !req_state && !anyA && k < np && next_ok) {
            if (k > 0) mem_check(k - 1, t);
            hk = k; hq = 0; hst = 1; hgap = 0; hnext = ((t / HCLK) + 1) * HCLK; Q.env.push({hnext, -2, 0, -1});
        }
        if (hostport && hst > 0) {   // the sequencer runs on its own clock, whatever the kernel's acknowledges do
            auto& W_ = HFILL[hk];
            while (hst > 0 && t >= hnext) {
                ll e = hnext; hnext += HCLK;
                if (hq >= (ll)W_.size()) { hst = 0; hnext = e; break; }
                const HostP& h = HOSTS[get<0>(W_[hq])]; bool hs = val(h.ack, e - 2 * HCLK);
                if (hst == 1) { if (hgap > 0) { hgap--; continue; }
                    unsigned ad = get<1>(W_[hq]), w = get<2>(W_[hq]);
                    for (size_t i = 0; i < h.addr.size(); i++) if (h.addr[i] >= 0) env_set(e + 1, h.addr[i], (ad >> i) & 1);
                    for (size_t i = 0; i < h.wdata.size() && i < 32; i++) if (h.wdata[i] >= 0) env_set(e + 1, h.wdata[i], (w >> i) & 1);
                    if (h.we >= 0) env_set(e + 1, h.we, true); hst = 2; }
                else if (hst == 2) { if (!hs) { env_set(e + 1, h.req, true); hst = 3; } }
                else if (hst == 3) { if (hs) { env_set(e + 1, h.req, false); hst = 4; } }
                else if (hst == 4) { if (!hs) { hq++; hst = 1; hgap = HGAP; nhost++; } }
            }
            if (hst > 0) { Q.env.push({hnext, -2, 0, -1}); continue; }
        }
        if (!req_state && !anyA && k < np && next_ok) {
            if (memf && !hostport) { if (k > 0) mem_check(k - 1, t); mem_fill(k, t); }   // the host reads back call k-1, fills call k
            if (hostport) hst = 0;
            if (datachange == "next" && k > 0) {
                drive_data(t + hostd, pairs[k].first, 0); drive_data(t + hostd, pairs[k].second, 1); drive_x(t + hostd, k, -1);
                env_set(t + hostd + max(su, 1LL), req, true);
            } else {
                // a host never raises a request before its data (bundled data at the boundary): with --datachange broad
                // the data of pair k was driven at data_at (hostdelay after its ack fell); the request comes su after
                // both. (Before 2026-11-16 21:5x the request could precede the data when hostdelay > the time to the
                // next offer, a boundary violation by the harness: FOR-RESEARCH C21 was that artefact.)
                ll tr = t + max(su, 1LL) + (k > 0 ? reqgap : 0);
                if (datachange == "broad" && k > 0) tr = max(tr, data_at + max(su, 1LL));
                env_set(tr, req, true);
            }
            req_state = true;
        } else if (req_state && allA && val(req, t)) {
            env_set(t + 1, req, false);
            req_state = false; k++; done_in++;
            if (k < np && datachange == "handshake") { drive_data(t + 2, pairs[k].first, 0); drive_data(t + 2, pairs[k].second, 1); drive_x(t + 2, k, -1); }
            if (!pipelined) next_ok = false;
        }
        bool r0 = val(oR, t);
        if (r0 && !val(oA, t) && !out_pending) {
            out_pending = true;
            env_set(t + dout, oA, true);
            Q.env.push({t + dout, -2, 0, -1});
            has_sample = true; sample_at = t + dout - 1;
        }
        if (has_sample && t >= sample_at) {
            ull v = 0;
            for (size_t i = 0; i < Bdata[2].size(); i++) if (val(Bdata[2][i], sample_at)) { if (i >= 64) die("out0 wider than 64 bits"); v += 1ULL << i; }
            outvals.push_back({sample_at, v});
            printf("out0 #%zu at %lld ps: %llu\n", outvals.size() - 1, sample_at, v);
            has_sample = false;
            if (!pipelined && nextreq == "sample") next_ok = true;
        }
        if (!r0 && val(oA, t) && out_pending) {
            out_pending = false;
            env_set(t + dfall, oA, false);
            if (!pipelined && nextreq == "seq") seq_wait = true;
        }
        if (seq_wait && !r0 && !val(oA, t)) { seq_wait = false; next_ok = true; Q.env.push({t + 1, -2, 0, -1}); }
        bool pr = val(req, t);
        if (pr != pend_state) { pend_state = pr; if (eA >= 0) env_set(t + (pr ? dout : dfall), eA, pr); }
    }
    fprintf(stderr, "sim: %lld events, t = %lld ps, %lld pairs offered, %lld accepted, %zu outputs\n", nev, t, np, done_in, outvals.size());
    bool ramok = true;
    if (!RAMS.empty()) {
        if (memf && (ll)outvals.size() == np && np > 0) mem_check(np - 1, t + 1);
        for (size_t id = 0; id < RAMS.size(); id++) if (RAMS[id].master >= 0) ram_step(id, t + 1);
        ram_checks();
        size_t ned = 0; for (auto& r : RAMS) ned += r.edges.size();
        fprintf(stderr, "RAMCHECK: %zu RAMs, %zu clock edges, setup/hold violations %lld %s; memory words checked %lld, wrong %lld %s; host writes %lld\n",
                RAMS.size(), ned, RAMVIOL, RAMVIOL_EX.c_str(), memchk, memmis, memex.c_str(), nhost);
        { const char* cn[3] = {"ADDR", "WE", "DI"}; string m_;
          for (int c = 0; c < 3; c++) for (int j = 0; j < 2; j++) if (RAMMIN[c][j] < (1LL << 49)) {
              char b[400]; snprintf(b, sizeof b, "%s%s %s %lld ps (%s)", m_.empty() ? "" : "; ", cn[c], j ? "hold" : "setup", RAMMIN[c][j], RAMMIN_AT[c][j].c_str()); m_ += b; }
          fprintf(stderr, "RAMMARGIN (beyond prjxray's widest setup / hold): %s\n", m_.c_str()); }
        ramok = RAMVIOL == 0 && memmis == 0;
    }
    if (W) {
        size_t nlut = 0; for (int g = 0; g < NG; g++) nlut += glut[g];
        vector<tuple<ll, string, int>> iv; for (auto& x : INF) iv.push_back({x.second, names[gout[x.first.first]], x.first.second});
        sort(iv.rbegin(), iv.rend());
        string s = "[";
        for (size_t i = 0; i < iv.size() && i < 5; i++) { char b[512]; snprintf(b, sizeof b, "%s(%lld, '%s', %d)", i ? ", " : "", get<0>(iv[i]), get<1>(iv[i]).c_str(), get<2>(iv[i])); s += b; }
        s += "]";
        fprintf(stderr, "HRUNT w=%d: LUT gates %zu, skipped reads %lld, INFEASIBLE pins %zu %s\n", W, nlut, NSKIP, INF.size(), s.c_str());
    }
    {   // NEARMISS (2026-11-17, informational, no verdict): pulses on the outputs of storage LUTs (a LUT reading its own
        // output: C-elements, latches, arbiter state) after reset. A state node that flips and flips back within a few
        // tens of ps came that close to a different outcome in this run. Transparent latches pass D glitches legitimately,
        // so a narrow pulse is a pointer for tracing, not a failure. Widths in ps; NEARMISS_PS (default 200) is the count bound.
        const char* nm = getenv("NEARMISS_PS"); ll NB = nm ? atoll(nm) : 200;
        vector<int> DRV0(NN, -1); for (int g = 0; g < NG; g++) DRV0[gout[g]] = g;
        vector<tuple<ll, ll, int>> pl; ll cnt = 0;   // (width, time of the first edge, node)
        for (int g = 0; g < NG; g++) {
            if (!glut[g]) continue;
            int o = gout[g]; bool st = false;
            for (int i = gins0[g]; i < gins0[g + 1]; i++) { int u = ins[i];
                for (int d = 0; d < 200 && u != o; d++) { int h = DRV0[u]; if (h < 0 || glut[h] || gk[h] != 1 || initw[ginit0[h]] != 2) break; u = ins[gins0[h]]; }
                if (u == o) { st = true; break; } }
            if (!st) continue;
            const vector<int>& h = H[o]; ll best = -1, bt = 0;
            for (size_t i = 1; i < h.size(); i++) {
                if (h[i - 1] < R + 5000) continue;   // start-up settling after reset release
                ll wdt = (ll)h[i] - h[i - 1];
                if (wdt < NB) cnt++;
                if (best < 0 || wdt < best) { best = wdt; bt = h[i - 1]; }
            }
            if (best >= 0) pl.push_back({best, bt, o});
        }
        sort(pl.begin(), pl.end());
        string s = "[";
        for (size_t i = 0; i < pl.size() && i < 3; i++) { char b[512]; snprintf(b, sizeof b, "%s(%lld, '%s', %lld)", i ? ", " : "", get<0>(pl[i]), names[get<2>(pl[i])].c_str(), get<1>(pl[i])); s += b; }
        fprintf(stderr, "NEARMISS storage-output pulses < %lld ps: %lld; narrowest (width, node, t) %s]\n", NB, cnt, s.c_str());
    }
    if (RACEON) for (int c = 0; c < 2; c++) {
        vector<pair<ll, pair<int, int>>> v; for (auto& x : RACEMIN[c]) v.push_back({x.second, x.first});
        sort(v.begin(), v.end());
        string s = "[";
        for (size_t i = 0; i < v.size() && i < 5; i++) { int g = v[i].second.first, q = v[i].second.second; ll tt = 0;
            for (auto& r : RACEB[c]) if (r.g == g && r.q == q && r.gap == v[i].first) { tt = r.t; break; }
            char b[600]; snprintf(b, sizeof b, "%s(%lld, '%s', %d, '%s', %lld)", i ? ", " : "", v[i].first, names[gout[g]].c_str(), q, names[ins[gins0[g] + q]].c_str(), tt); s += b; }
        fprintf(stderr, "RACES %s within %lld ps: %lld events at %zu (gate, pin); closest (gap, gate, pin, pin's source, t) %s]\n",
                c ? "feeding-storage" : "storage", RACEX, RACEN[c], RACEMIN[c].size(), s.c_str());
    }
    if (capped) {
        fprintf(stderr, "simx: MAXEV cap %lld events hit at t = %lld ps: no verdict\n", maxev, t);
        fflush(stdout); return 3;
    }
    if (dump) {
        FILE* f = fopen(dump, "w"); if (!f) die("cannot write %s", dump);
        fprintf(f, "{\"tend\": %lld, \"nodes\": {", t);
        bool first = true;
        for (int n = 0; n < NN; n++) if (!H[n].empty() || V0[n]) {
            fprintf(f, "%s\"%d\": [%s, [", first ? "" : ", ", n, V0[n] ? "true" : "false"); first = false;
            for (size_t i = 0; i < H[n].size(); i++) fprintf(f, "%s%d", i ? ", " : "", H[n][i]);
            fprintf(f, "]]");
        }
        fprintf(f, "}, \"outs\": [");
        for (size_t i = 0; i < outvals.size(); i++) fprintf(f, "%s[%lld, %llu]", i ? ", " : "", outvals[i].first, outvals[i].second);
        fprintf(f, "], \"pairs\": [");
        for (size_t i = 0; i < pairs.size(); i++) fprintf(f, "%s[%llu, %llu]", i ? ", " : "", pairs[i].first, pairs[i].second);
        fprintf(f, "], \"args\": {\"net\": \"%s\", \"pairs\": [", netf);
        for (size_t i = 0; i < pairstr.size(); i++) fprintf(f, "%s\"%s\"", i ? ", " : "", pairstr[i].c_str());
        fprintf(f, "], \"corner\": %g, \"kappa\": %g, \"R\": %lld, \"w\": %d, \"classes\": \"%s\", \"cdefault\": \"%c\", \"su\": %lld, \"dout\": %lld, \"dfall\": %lld, \"tmax\": %lld, \"datachange\": \"%s\", \"nextreq\": \"%s\", \"data0\": %s, \"full\": true, \"sim\": \"simx\"}}",
                corner, kappa, R, W, classes, cdefault, su, dout, dfall, tmax, datachange.c_str(), nextreq.c_str(), data0 ? "true" : "false");
        fclose(f);
    }
    vector<ull> want, got;
    if (has_want) want = wantv;
    else for (auto& pq : pairs) { ull x = pq.first, y = pq.second; while (y) { ull r = x % y; x = y; y = r; } want.push_back(x); }
    for (auto& o : outvals) got.push_back(o.second);
    bool ok = got == want && ramok;
    printf("RESULT %s: want %s got %s\n", ok ? "OK" : "MISMATCH", pylist(want).c_str(), pylist(got).c_str());
    fflush(stdout);
    return ok ? 0 : 2;
}
