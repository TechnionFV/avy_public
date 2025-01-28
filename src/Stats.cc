#include "avy/Util/Stats.h"
#include "boost/format.hpp"

namespace avy {
std::map<std::string, unsigned> Stats::counters;
std::map<std::string, Stopwatch> Stats::sw;
std::map<std::string, Averager> Stats::av;
std::map<std::string, std::string> Stats::txt;

void Stats::count(const std::string &name) {
  if (counters.count(name) == 0) counters[name] = 0;
  ++counters[name];
}
void Stats::count(const std::string &name, unsigned count) {
  if (counters.count(name) == 0) counters[name] = 0;
  counters[name] += count;
}
double Stats::avg(const std::string &n, double v) { return av[n].add(v); }
unsigned Stats::uset(const std::string &n, unsigned v) {
  return counters[n] = v;
}
void Stats::set(const std::string &k, const std::string &v) { txt[k] = v; }
unsigned Stats::get(const std::string &n) { return counters[n]; }

void Stats::start(const std::string &name) { sw[name].start(); }
void Stats::stop(const std::string &name) { sw[name].stop(); }
void Stats::resume(const std::string &name) { sw[name].resume(); }

/** Outputs all statistics to std output */
void Stats::Print(std::ostream &OS) {
  for (auto kv : counters) OS << kv.first << ": " << kv.second << "\n";

  for (auto kv : sw) OS << kv.first << ": " << kv.second << "\n";

  for (auto kv : av) OS << kv.first << ": " << kv.second << "\n";

  for (auto &kv : txt) OS << kv.first << " " << kv.second << "\n";
}

void Stats::PrintBrunch(std::ostream &OS) {
  OS << "\n\n************** BRUNCH STATS ***************** \n";
  for (auto kv : counters)
    OS << "BRUNCH_STAT " << kv.first << " " << kv.second << "\n";

  for (auto kv : sw)
    OS << "BRUNCH_STAT " << kv.first << " "
       << (boost::format("%.2f") % (kv.second).toSeconds()) << "\n";

  for (auto kv : av)
    OS << "BRUNCH_STAT " << kv.first << " " << kv.second << "\n";

  for (auto &kv : txt)
    OS << "BRUNCH_STAT " << kv.first << " " << kv.second << "\n";

  OS << "************** BRUNCH STATS END ***************** \n";
}

void Averager::Print(std::ostream &out) const {
  out << boost::format("%.2f") % avg << " (m: " << boost::format("%.2f") % min
      << ", "
      << "M: " << boost::format("%.2f") % max << ")";
}

} // namespace avy
