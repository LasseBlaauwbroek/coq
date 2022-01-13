#include <sys/resource.h>
#include <sys/syscall.h>
#include <unistd.h>
#include <sched.h>
#ifndef SCHED_IDLE
#define SCHED_IDLE	5
#endif
#define CAML_NAME_SPACE
#include "caml/mlvalues.h"

CAMLprim value low_priority()
{
  struct sched_param sp = { .sched_priority = 0 };
  int tid;

  /* tid = syscall(SYS_gettid); */
  /* setpriority(PRIO_PROCESS, tid, 100); */
  sched_setscheduler(0, SCHED_IDLE, &sp);

  return Val_unit;
}
