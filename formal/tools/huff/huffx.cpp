// Shard C (UNTRUSTED explorer): exhaustive state-space search of THE target's Huffman abstraction.
// Model (as tools/cview/hufsim.py): state = storage nodes (4,597) + environment nodes; all other logic
// zero-delay. Moves: (a) fire one excited CONTROL storage node (not latch-like), (b) one move of the
// sequential four-phase environment (each env signal is its own move, any delay). After every move,
// "latches first": excited latch-like storage nodes fire (Jacobi rounds) until none is excited.
// Every interleaving of (a) and (b) is explored (DFS, states hashed: 128-bit Zobrist, bit-state; a
// collision could hide a state, so this is evidence, not proof).
// Checks: (1) out0 data at every out0 ack rise = gcd of that pair; (2) persistence: a control node
// excited in a state stays excited after any other move; (3) deadlock: no move and not finished;
// (4) latch closure converges.
// usage: huffx prep.txt a,b [a,b ...] [--max N]
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
struct G { int out, k; vector<int> ins; vector<u64> init; bool latch; int rank; };
int NN; vector<string> names; vector<G> comb, stor; vector<int> combOf, storOf; // node -> index or -1
vector<vector<int>> fanComb, fanStor; // node -> comb gates / storage gates reading it
int RST, REQ, AACK, BACK, SACK, OREQ, OACK, PACK; vector<int> AD, BD, OD;
vector<unsigned char> val; vector<u64> Z1, Z2; u64 H1 = 0, H2 = 0;
vector<pair<u64, u64>> pairsv; int NP;
static inline bool bitAt(const vector<u64>& I, unsigned a) { return (I[a >> 6] >> (a & 63)) & 1; }
static inline bool evalG(const G& g) {
  unsigned a = 0; for (int j = 0; j < g.k; j++) if (val[g.ins[j]]) a |= 1u << j; return bitAt(g.init, a);
}
vector<int> trail; // nodes changed (for undo): push node id, old value stored implicitly (flip)
static inline void setNode(int n, bool v) {
  if (val[n] == v) return; val[n] = v; trail.push_back(n);
  if (storOf[n] >= 0 || n == REQ || n == OACK || n == PACK || n == RST) { H1 ^= Z1[n]; H2 ^= Z2[n]; }
}
// event-driven settle of comb logic from changed nodes
vector<vector<int>> buckets; int maxRank = 0; vector<char> inq;
void settleFrom(const vector<int>& changed) {
  int lo = INT_MAX;
  for (int n : changed) for (int c : fanComb[n]) if (!inq[c]) { inq[c] = 1; buckets[comb[c].rank].push_back(c); lo = min(lo, comb[c].rank); }
  if (lo == INT_MAX) return;
  for (int r = lo; r <= maxRank; r++) {
    for (size_t i = 0; i < buckets[r].size(); i++) {
      int c = buckets[r][i]; inq[c] = 0; const G& g = comb[c]; bool nv = evalG(g);
      if (nv != (bool)val[g.out]) {
        setNode(g.out, nv);
        for (int d : fanComb[g.out]) if (!inq[d]) { inq[d] = 1; buckets[comb[d].rank].push_back(d); }
      }
    }
    buckets[r].clear();
  }
}
bool excited(int s) { return evalG(stor[s]) != (bool)val[stor[s].out]; }
bool latchClosure() {
  for (int round = 0; round < 100000; round++) {
    vector<int> ex;
    for (int s = 0; s < (int)stor.size(); s++) if (stor[s].latch && excited(s)) ex.push_back(s);
    if (ex.empty()) return true;
    vector<int> ch;
    for (int s : ex) { setNode(stor[s].out, !val[stor[s].out]); ch.push_back(stor[s].out); }
    settleFrom(ch);
  }
  return false;
}
// faster closure: only check latches reading changed nodes
vector<int> markLatch;
bool latchClosureFrom(size_t trailStart) {
  for (int round = 0; round < 100000; round++) {
    vector<int> ex; set<int> cand;
    for (size_t i = trailStart; i < trail.size(); i++) for (int s : fanStor[trail[i]]) if (stor[s].latch) cand.insert(s);
    for (int s : cand) if (excited(s)) ex.push_back(s);
    if (ex.empty()) return true;
    trailStart = trail.size();
    vector<int> ch;
    for (int s : ex) { setNode(stor[s].out, !val[stor[s].out]); ch.push_back(stor[s].out); }
    settleFrom(ch);
  }
  return false;
}
void undoTo(size_t m) {
  while (trail.size() > m) { int n = trail.back(); trail.pop_back(); val[n] = !val[n];
    if (storOf[n] >= 0 || n == REQ || n == OACK || n == PACK || n == RST) { H1 ^= Z1[n]; H2 ^= Z2[n]; } }
}
u64 busv(const vector<int>& d) { u64 v = 0; for (size_t i = 0; i < d.size(); i++) if (val[d[i]]) v |= 1ull << i; return v; }
// env state beyond node values
struct EnvS { int k, kout; int w; };
EnvS env;
struct Key { u64 a, b; bool operator==(const Key& o) const { return a == o.a && b == o.b; } };
struct KH { size_t operator()(const Key& k) const { return k.a ^ (k.b * 0x9e3779b97f4a7c15ull); } };
unordered_set<Key, KH> seen;
long long nTriOK = 0, nTriBad = 0; map<int,long long> triWhy; vector<pair<int,int>> rtPairs; long long nRtBlock = 0; map<string,long long> rtBlockBy; bool triCheck = false;
long long nStates = 0, nDead = 0, nWrong = 0, nPersist = 0, nFinal = 0, maxStates;
map<string, long long> persistBy; long long maxDepth = 0;
vector<int> ctl;
Key key() { return Key{H1 ^ (u64)env.k * 0x51ed27, H2 ^ (u64)env.kout * 0x2545f491}; }
void setBus(int k) {
  for (size_t i = 0; i < AD.size(); i++) setNode(AD[i], (pairsv[k].first >> i) & 1);
  for (size_t i = 0; i < BD.size(); i++) setNode(BD[i], (pairsv[k].second >> i) & 1);
}
// moves: id >= 0: fire ctl storage stor[id]; -1 req rise, -2 req fall, -3 pack rise, -4 pack fall, -5 oack rise, -6 oack fall
vector<int> moves() {
  vector<int> m;
  for (int s : ctl) if (excited(s)) m.push_back(s);
  bool req = val[REQ], pa = val[PACK], oa = val[OACK], orq = val[OREQ];
  if (!req && !val[AACK] && !val[BACK] && !val[SACK] && !pa && env.k < NP && env.k <= env.kout && !orq && !oa) m.push_back(-1);
  if (req && val[AACK] && val[BACK] && val[SACK] && pa) m.push_back(-2);
  if (req && !pa) m.push_back(-3);
  if (!req && pa) m.push_back(-4);
  if (orq && !oa) m.push_back(-5);
  if (!orq && oa) m.push_back(-6);
  return m;
}
bool apply(int mv, EnvS& e) { // returns false on a wrong result
  size_t t0 = trail.size(); vector<int> ch;
  if (mv >= 0) { int n = stor[mv].out; setNode(n, !val[n]); ch.push_back(n); }
  else if (mv == -1) { setBus(e.k); setNode(REQ, 1); e.k++; for (int x : AD) ch.push_back(x); for (int x : BD) ch.push_back(x); ch.push_back(REQ); }
  else if (mv == -2) { setNode(REQ, 0); ch.push_back(REQ); e.w = 1; }
  else if (mv == -3) { setNode(PACK, 1); ch.push_back(PACK); }
  else if (mv == -4) { setNode(PACK, 0); ch.push_back(PACK); }
  else if (mv == -5) {
    u64 got = busv(OD), want = std::gcd(pairsv[e.kout].first, pairsv[e.kout].second);
    if (got != want) { nWrong++; if (nWrong < 5) fprintf(stderr, "WRONG out0 pair %d got %llu want %llu\n", e.kout, got, want); }
    setNode(OACK, 1); ch.push_back(OACK); e.kout++;
  }
  else if (mv == -6) { setNode(OACK, 0); ch.push_back(OACK); e.w = 0; }
  settleFrom(ch);
  if (!latchClosureFrom(t0)) { fprintf(stderr, "latch closure did not converge\n"); exit(3); }
  return true;
}
void dfs(int depth) {
  vector<int> ms = moves();
  maxDepth = max(maxDepth, (long long)depth);
  if (ms.empty()) {
    bool fin = env.k == NP && env.kout == NP && !val[REQ] && !val[PACK] && !val[OACK] && !val[OREQ];
    if (fin) nFinal++; else { nDead++; if (nDead < 5) fprintf(stderr, "DEADLOCK depth %d k %d kout %d\n", depth, env.k, env.kout); }
    return;
  }
  vector<int> exc; for (int m : ms) if (m >= 0) exc.push_back(m);
  for (int mv : ms) {
    size_t mark = trail.size(); EnvS save = env; u64 h1 = H1, h2 = H2;
    apply(mv, env);
    // persistence: every other excited ctl node still excited
    for (int s : exc) if (s != mv && !excited(s)) { nPersist++; persistBy[names[stor[s].out] + (mv >= 0 ? " by " + names[stor[mv].out] : " by env" + to_string(mv))]++; }
    Key kk = key();
    if (seen.insert(kk).second) {
      nStates++;
      if (nStates % 1000000 == 0) fprintf(stderr, "  %lld states, depth %d\n", nStates, depth);
      if (nStates < maxStates) dfs(depth + 1);
    }
    undoTo(mark); env = save; H1 = h1; H2 = h2;
  }
}
string traceDir; map<string,int> traceCnt; int traceK = 5;
string rtFile, dumpInit, winFile, obsOut, traceNode, traceOut; int walks = 0; long long walkSeed = 1, walkRange = 64;
int main(int argc, char** argv) {
  ifstream in(argv[1]); string w; int n;
  maxStates = 50000000;
  for (int i = 2; i < argc; i++) {
    string a = argv[i];
    if (a == "--max") { maxStates = atoll(argv[++i]); continue; }
    if (a == "--dump-init") { dumpInit = argv[++i]; continue; }
    if (a == "--walks") { walks = atoi(argv[++i]); winFile = argv[++i]; obsOut = argv[++i]; continue; }
    if (a == "--trace") { traceNode = argv[++i]; traceOut = argv[++i]; continue; }
    if (a == "--traceall") { traceDir = argv[++i]; traceK = atoi(argv[++i]); continue; }
    if (a == "--tri") { triCheck = true; continue; }
    if (a == "--rt") { rtFile = argv[++i]; continue; }
    if (a == "--seed") { walkSeed = atoll(argv[++i]); continue; }
    if (a == "--range") { walkRange = atoll(argv[++i]); continue; }
    size_t c = a.find(','); pairsv.push_back({stoull(a.substr(0, c), 0, 0), stoull(a.substr(c + 1), 0, 0)});
  }
  NP = pairsv.size();
  in >> w >> NN; names.resize(NN); { string l0; getline(in, l0); } for (int i = 0; i < NN; i++) getline(in, names[i]);
  auto readG = [&](bool st) { G g; in >> g.out >> g.k; g.ins.resize(g.k); for (int j = 0; j < g.k; j++) in >> g.ins[j];
    string hx; in >> hx; int nb = 1 << g.k; g.init.assign((nb + 63) / 64, 0);
    for (int b = 0; b < (int)hx.size(); b++) { int d = hx[hx.size() - 1 - b]; d = isdigit(d) ? d - '0' : d - 'a' + 10;
      for (int q = 0; q < 4; q++) if ((d >> q) & 1) { int bit = 4 * b + q; if (bit < nb) g.init[bit >> 6] |= 1ull << (bit & 63); } }
    if (st) { int l; in >> l; g.latch = l; } else g.latch = false; return g; };
  in >> w >> n; for (int i = 0; i < n; i++) comb.push_back(readG(false));
  in >> w >> n; for (int i = 0; i < n; i++) stor.push_back(readG(true));
  in >> w; map<string, int> bnd; for (int i = 0; i < 8; i++) { string kv; in >> kv; size_t e = kv.find('='); bnd[kv.substr(0, e)] = stoi(kv.substr(e + 1)); }
  RST = bnd["rst"]; REQ = bnd["req"]; AACK = bnd["a_ack"]; BACK = bnd["b_ack"]; SACK = bnd["start_ack"]; OREQ = bnd["out0_req"]; OACK = bnd["out0_ack"]; PACK = bnd["pend_ack"];
  string line; getline(in, line);
  auto readList = [&](vector<int>& v) { getline(in, line); istringstream ss(line); string t; ss >> t; int x; while (ss >> x) v.push_back(x); };
  readList(AD); readList(BD); readList(OD);
  combOf.assign(NN, -1); storOf.assign(NN, -1); fanComb.resize(NN); fanStor.resize(NN);
  // ranks
  vector<int> rk(NN, 0);
  for (size_t c = 0; c < comb.size(); c++) { combOf[comb[c].out] = c; }
  for (size_t s = 0; s < stor.size(); s++) storOf[stor[s].out] = s;
  for (size_t c = 0; c < comb.size(); c++) { int r = 0; for (int x : comb[c].ins) if (combOf[x] >= 0) r = max(r, rk[x] + 1); rk[comb[c].out] = r; comb[c].rank = r; maxRank = max(maxRank, r); }
  for (size_t c = 0; c < comb.size(); c++) { set<int> u(comb[c].ins.begin(), comb[c].ins.end()); for (int x : u) fanComb[x].push_back(c); }
  for (size_t s = 0; s < stor.size(); s++) { set<int> u(stor[s].ins.begin(), stor[s].ins.end()); for (int x : u) fanStor[x].push_back(s); }
  buckets.resize(maxRank + 1); inq.assign(comb.size(), 0);
  mt19937_64 rng(12345); Z1.resize(NN); Z2.resize(NN); for (int i = 0; i < NN; i++) { Z1[i] = rng(); Z2[i] = rng(); }
  for (size_t s = 0; s < stor.size(); s++) if (!stor[s].latch) ctl.push_back(s);
  val.assign(NN, 0);
  for (auto& g : comb) val[g.out] = evalG(g);   // topological order (prep emits rank order)
  // reset: rst high, fire excited storage nodes in index order until stable, then rst low
  setBus(0);
  { vector<int> ch(AD); ch.insert(ch.end(), BD.begin(), BD.end()); settleFrom(ch); }
  setNode(RST, 1); settleFrom({RST});
  auto stabilize = [&]() { for (int it = 0; it < 1000000; it++) { int f = -1; for (size_t s = 0; s < stor.size(); s++) if (excited(s)) { f = s; break; }
      if (f < 0) return true; setNode(stor[f].out, !val[stor[f].out]); settleFrom({stor[f].out}); } return false; };
  if (!stabilize()) { fprintf(stderr, "reset did not settle\n"); return 2; }
  setNode(RST, 0); settleFrom({RST});
  if (!stabilize()) { fprintf(stderr, "post-reset did not settle\n"); return 2; }
  trail.clear();
  fprintf(stderr, "huffx: %d nodes, %zu comb (depth %d), %zu storage, %zu control; %d pairs\n", NN, comb.size(), maxRank, stor.size(), ctl.size(), NP);
  if (!dumpInit.empty()) { FILE* f = fopen(dumpInit.c_str(), "w"); for (int i = 0; i < NN; i++) fputc(val[i] ? '1' : '0', f); fputc('\n', f); fclose(f); if (maxStates == 0) return 0; }
  env = {0, 0, 0};
  if (!rtFile.empty()) { map<string,int> byName; for (size_t q = 0; q < stor.size(); q++) byName[names[stor[q].out]] = q;
    ifstream rf(rtFile); string a1, b1; while (rf >> a1 >> b1) rtPairs.push_back({byName.at(a1), byName.at(b1)});
    fprintf(stderr, "relative-timing pairs: %zu\n", rtPairs.size()); }
  if (walks > 0) {
    // random walks: record the tuple of every window (winfix.py --export) in every visited state
    ifstream wf(winFile); int nw; wf >> nw; vector<string> wk(nw); vector<vector<int>> wv(nw);
    for (int i = 0; i < nw; i++) { int n; wf >> wk[i] >> n; wv[i].resize(n); for (int j = 0; j < n; j++) wf >> wv[i][j]; }
    vector<unordered_set<u64>> obs(nw);
    auto record = [&]() { for (int i = 0; i < nw; i++) { u64 t = 0; for (size_t j = 0; j < wv[i].size(); j++) { int v = wv[i][j]; bool b = v < 0 ? env.w : val[v]; if (b) t |= 1ull << j; } obs[i].insert(t); } };
    vector<unsigned char> val0 = val; mt19937_64 rg(walkSeed);
    long long tot = 0, okc = 0;
    for (int w = 0; w < walks; w++) {
      val = val0; env = {0, 0, 0}; H1 = H2 = 0; trail.clear();
      // operand pairs for this walk: drawn from a small range so that runs finish
      pairsv.clear(); for (int q = 0; q < NP; q++) { u64 a = rg() % walkRange, b = rg() % walkRange; pairsv.push_back({a, b}); }
      setBus(0); { vector<int> ch(AD); ch.insert(ch.end(), BD.begin(), BD.end()); settleFrom(ch); latchClosureFrom(0); }
      trail.clear(); record();
      vector<int> hist;
      for (long long st = 0; st < 10000000; st++) {
        vector<int> ms = moves(); if (ms.empty()) break;
        if (!rtPairs.empty()) {   // relative timing: b may not move while its partner c is excited
          vector<int> ms2;
          for (int m : ms) { bool blocked = false; if (m >= 0) for (auto& pr : rtPairs) if (pr.second == m && excited(pr.first)) { blocked = true; break; } if (!blocked) ms2.push_back(m); }
          if (!ms2.empty()) ms = ms2;
        }
        int mv = ms[rg() % ms.size()];
        vector<int> exc; for (int m : ms) if (m >= 0 && m != mv) exc.push_back(m);
        auto blockedNow = [&](int m) { for (auto& pr : rtPairs) if (pr.second == m && excited(pr.first)) return true; return false; };
        size_t mk0 = trail.size(); EnvS es0 = env; u64 h10 = H1, h20 = H2;
        apply(mv, env);
        if (triCheck) {
          // for every control node c excited before mv and disabled by it: does s.c.mv.c = s.mv ?
          vector<int> dis; for (int c : exc) if (!excited(c)) dis.push_back(c);
          if (!dis.empty()) {
            Key kb = key(); size_t mkb = trail.size(); EnvS eb = env; u64 hb1 = H1, hb2 = H2;
            vector<unsigned char> vb(val);
            for (int c : dis) {
              // back to s
              undoTo(mk0); env = es0; H1 = h10; H2 = h20;
              bool ok = true; EnvS e2 = env; int why = 0;
              apply(c, e2);
              vector<int> m2 = moves(); if (find(m2.begin(), m2.end(), mv) == m2.end()) { ok = false; why = 1; }
              if (ok) { apply(mv, e2); if (!excited(c)) { ok = false; why = 2; } else { apply(c, e2); env = e2; Key k3 = key(); ok = (k3 == kb); if (!ok) why = 3; } }
              triWhy[why]++;
              if (ok) nTriOK++; else { nTriBad++; if (nTriBad < 10) fprintf(stderr, "TRIANGLE FAILS: %s vs %s\n", names[stor[c].out].c_str(), mv >= 0 ? names[stor[mv].out].c_str() : "env"); }
            }
            // restore s.mv
            undoTo(mk0); env = es0; H1 = h10; H2 = h20; apply(mv, env);
            if (!(key() == kb)) { fprintf(stderr, "restore mismatch\n"); exit(4); }
          }
        }
        trail.clear(); record(); tot++; hist.push_back(mv); if (traceNode.empty() && traceDir.empty() && hist.size() > 64) hist.erase(hist.begin());
        if (!rtPairs.empty()) for (int c : exc) if (excited(c) && blockedNow(c)) { nRtBlock++; rtBlockBy[names[stor[c].out] + (mv >= 0 ? " by " + names[stor[mv].out] : " by env" + to_string(mv))]++; }
        for (int c : exc) if (!excited(c)) { if (nPersist < 40) { fprintf(stderr, "VIOL walk %d move %lld: %s (val %d) disabled by %s; env k %d kout %d w %d req %d pack %d oreq %d oack %d; last moves:", w, st, names[stor[c].out].c_str(), (int)val[stor[c].out], mv >= 0 ? names[stor[mv].out].c_str() : ("env" + to_string(mv)).c_str(), env.k, env.kout, env.w, (int)val[REQ], (int)val[PACK], (int)val[OREQ], (int)val[OACK]); for (size_t q = hist.size() > 8 ? hist.size() - 8 : 0; q < hist.size(); q++) fprintf(stderr, " %s", hist[q] >= 0 ? names[stor[hist[q]].out].c_str() : ("env" + to_string(hist[q])).c_str()); fprintf(stderr, "\n"); }
          if (!traceDir.empty()) {
            string key2 = names[stor[c].out] + "__" + (mv >= 0 ? names[stor[mv].out] : "env");
            if (traceCnt[key2]++ < traceK) {
              string fn = traceDir + "/" + key2 + "__" + to_string(traceCnt[key2]) + ".txt";
              FILE* tf = fopen(fn.c_str(), "w");
              fprintf(tf, "# huffx trace: walk %d seed %lld\n", w, walkSeed);
              for (size_t q = 0; q < hist.size(); q++) fprintf(tf, "%s\n", hist[q] >= 0 ? names[stor[hist[q]].out].c_str() : ("env" + to_string(hist[q])).c_str());
              fclose(tf);
            }
          }
          if (!traceNode.empty() && names[stor[c].out] == traceNode) {
            FILE* tf = fopen(traceOut.c_str(), "w");
            fprintf(tf, "# huffx trace: walk %d seed %lld range %lld pairs", w, walkSeed, walkRange);
            for (auto& pr : pairsv) fprintf(tf, " %llu,%llu", pr.first, pr.second);
            fprintf(tf, "\n# %s (val %d) excited, then disabled by the last move\n", traceNode.c_str(), (int)val[stor[c].out]);
            for (size_t q = 0; q < hist.size(); q++) fprintf(tf, "%s\n", hist[q] >= 0 ? names[stor[hist[q]].out].c_str() : ("env" + to_string(hist[q])).c_str());
            fclose(tf); fprintf(stderr, "trace written (%zu moves)\n", hist.size()); exit(0);
          }
          nPersist++; persistBy[names[stor[c].out] + (mv >= 0 ? " by " + names[stor[mv].out] : " by env" + to_string(mv))]++; }
      }
      if (env.kout == NP) okc++;
    }
    long long sz = 0; for (auto& o : obs) sz += o.size();
    fprintf(stderr, "walks %d (complete %lld), moves %lld, wrong %lld, persistence violations %lld, observed tuples %lld; triangle ok %lld fail %lld (why1 mv disabled by c %lld, why2 c not re-excited %lld, why3 states differ %lld)\n", walks, okc, tot, nWrong, nPersist, sz, nTriOK, nTriBad, triWhy[1], triWhy[2], triWhy[3]);
    for (auto& kv : persistBy) fprintf(stderr, "  persist %lld %s\n", kv.second, kv.first.c_str());
    fprintf(stderr, "enabled moves newly blocked by a priority: %lld\n", nRtBlock);
    for (auto& kv : rtBlockBy) fprintf(stderr, "  rtblock %lld %s\n", kv.second, kv.first.c_str());
    FILE* f = fopen(obsOut.c_str(), "w");
    for (int i = 0; i < nw; i++) { fprintf(f, "%s", wk[i].c_str()); for (u64 t : obs[i]) fprintf(f, " %llu", t); fprintf(f, "\n"); }
    fclose(f); return 0;
  }
  seen.insert(key()); nStates = 1;
  dfs(0);
  printf("states %lld (cap %lld)%s maxdepth %lld final %lld deadlocks %lld wrong %lld persistence-violations %lld\n",
         nStates, maxStates, nStates >= maxStates ? " CAPPED" : "", maxDepth, nFinal, nDead, nWrong, nPersist);
  int c = 0; for (auto& kv : persistBy) { if (c++ < 30) printf("  persist %lld %s\n", kv.second, kv.first.c_str()); }
  return 0;
}
