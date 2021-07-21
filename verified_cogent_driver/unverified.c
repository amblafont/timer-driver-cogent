
#define TIMER_BASE      0xc1100000
#define TIMER_MAP_BASE  0xc1109000

#define TIMER_REG_START   0x2650    // TIMER_MUX

typedef unsigned int    uint32_t;
typedef uint32_t uintptr_t;

typedef struct {
    void *vaddr;
} meson_timer_config_t;

#include "generated/driver.cogent"

/*

The device contains 5 timers, A,B C,D,E, but the driver only use timer A and E.
Timer E is a chronomoter while timer A is a countdown.

*/
int meson_init(meson_timer_t *timer, meson_timer_config_t config)
{
    // This won't appear in the cogent code (we assume that
    // we are given non null pointers
    if (timer == NULL || config.vaddr == NULL) {
        return EINVAL;
    }

    timer->regs = (void *)((uintptr_t) config.vaddr + (TIMER_BASE + TIMER_REG_START * 4 - TIMER_MAP_BASE));
    initialize(timer);
    return 0;
}
   
