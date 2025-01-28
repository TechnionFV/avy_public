#ifndef _STATS__H_
#define _STATS__H_

#include <map>

#include <sys/resource.h>
#include <sys/time.h>

#include <boost/foreach.hpp>
#define foreach BOOST_FOREACH

#include <iostream>

namespace avy {
class Stopwatch {
private:
  long started;
  long finished;
  long timeElapsed;

  long systemTime() const {
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    long r = ru.ru_utime.tv_sec * 1000000L + ru.ru_utime.tv_usec;
    return r;
  }

public:
  Stopwatch() { start(); }

  void start() {
    started = systemTime();
    finished = -1;
    timeElapsed = 0;
  }

  void stop() {
    if (finished < started) { finished = systemTime(); }
  }

  void resume() {
    if (finished >= started) {
      timeElapsed += finished - started;
      started = systemTime();
      finished = -1;
    }
  }

  long getTimeElapsed() const {
    if (finished < started) return timeElapsed + systemTime() - started;
    return timeElapsed + finished - started;
  }

  void Print(std::ostream &out) const {
    long time = getTimeElapsed();
    long h = time / 3600000000L;
    long m = time / 60000000L - h * 60;
    float s = ((float)time / 1000000L) - m * 60 - h * 3600;

    if (h > 0) out << h << "h";
    if (m > 0) out << m << "m";
    out << s << "s";
  }

  double toSeconds() {
    double time = ((double)getTimeElapsed() / 1000000);
    return time;
  }
};

/** Computes running average */
class Averager {
private:
  size_t count;
  double max;
  double min;
  double avg;

public:
  Averager() : count(0), avg(0) {}

  double add(double k) {
    if (count == 0) {
      min = k;
      max = k;
    }
    avg += (k - avg) / (++count);
    min = std::min(k, min);
    max = std::max(k, max);

    return avg;
  }

  void Print(std::ostream &out) const;
};

} // namespace avy

namespace avy {
inline std::ostream &operator<<(std::ostream &OS, const Stopwatch &sw) {
  sw.Print(OS);
  return OS;
}

inline std::ostream &operator<<(std::ostream &OS, const Averager &av) {
  av.Print(OS);
  return OS;
}

class Stats {
private:
  static std::map<std::string, unsigned> counters;
  static std::map<std::string, Stopwatch> sw;
  static std::map<std::string, Averager> av;
  static std::map<std::string, std::string> txt;

public:
  static unsigned get(const std::string &n);
  static double avg(const std::string &n, double v);
  static unsigned uset(const std::string &n, unsigned v);
  static void set(const std::string &k, const std::string &v);

  static void count(const std::string &name);
  static void count(const std::string &name, unsigned count);

  static void start(const std::string &name);
  static void stop(const std::string &name);
  static void resume(const std::string &name);

  /** Outputs all statistics to std output */
  static void Print(std::ostream &OS);
  static void PrintBrunch(std::ostream &OS);
};

class ScoppedStats {
  std::string m_name;

public:
  ScoppedStats(const std::string &name, bool reset = false) : m_name(name) {
    if (reset) {
      m_name += ".last";
      Stats::start(m_name);
    } else
      Stats::resume(m_name);
  }
  ~ScoppedStats() { Stats::stop(m_name); }
};
} // namespace avy

// __PRETTY_FUNCTION__ can be used instead of __func__ to include class name
// but used as is it is too verbose. Maybe need to write an extractor from full
// name to extract only the information that we want
#define AVY_MEASURE_FN ScoppedStats __stats__(__func__)
#define AVY_MEASURE_FN_LAST ScoppedStats __stats_last__(__func__, true)

#endif
