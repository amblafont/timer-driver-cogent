// This file is generated by Cogent

#include "driver.h"

static inline void d5_set_timer_e_part0(t3 *b, unsigned int v)
{
    (*b).data[18U] = ((*b).data[18U] & ~(0XFFFFFFFFU << 0U)) | (0XFFFFFFFFU &
                                                                v) << 0U;
}
static inline void d4_set_timer_e(t3 *b, u32 v)
{
    d5_set_timer_e_part0(b, (unsigned int) (v >> 0U & 4294967295U));
}
static inline unsigned int d8_get_timer_e_hi_part0(t3 *b)
{
    return (*b).data[19U] >> 0U & 0XFFFFFFFFU;
}
static inline u32 d7_get_timer_e_hi(t3 *b)
{
    return (u32) d8_get_timer_e_hi_part0(b) << 0U;
}
static inline unsigned int d10_get_timer_e_part0(t3 *b)
{
    return (*b).data[18U] >> 0U & 0XFFFFFFFFU;
}
static inline u32 d9_get_timer_e(t3 *b)
{
    return (u32) d10_get_timer_e_part0(b) << 0U;
}
static inline void d14_set_timer_a_input_clk_tag_part0(t3 *b, unsigned int v)
{
    (*b).data[0U] = ((*b).data[0U] & ~(0X3U << 8U)) | (0X3U & v) << 8U;
}
static inline void d13_set_timer_a_input_clk_tag(t3 *b, unsigned int v)
{
    d14_set_timer_a_input_clk_tag_part0(b, (unsigned int) (v >> 0U & 3U));
}
static inline void d15_set_timer_a_input_clk_TIMEOUT_TIMEBASE_100_US(t3 *b,
                                                                     unit_t v)
{ }
static inline void d16_set_timer_a_input_clk_TIMEOUT_TIMEBASE_10_US(t3 *b,
                                                                    unit_t v)
{ }
static inline void d17_set_timer_a_input_clk_TIMEOUT_TIMEBASE_1_MS(t3 *b,
                                                                   unit_t v)
{ }
static inline void d18_set_timer_a_input_clk_TIMEOUT_TIMEBASE_1_US(t3 *b,
                                                                   unit_t v)
{ }
static inline void d12_set_timer_a_input_clk(t3 *b, t1 v)
{
    if (v.tag == TAG_ENUM_TIMEOUT_TIMEBASE_1_US) {
        d13_set_timer_a_input_clk_tag(b, 0U);
        d18_set_timer_a_input_clk_TIMEOUT_TIMEBASE_1_US(b,
                                                        v.TIMEOUT_TIMEBASE_1_US);
    } else if (v.tag == TAG_ENUM_TIMEOUT_TIMEBASE_1_MS) {
        d13_set_timer_a_input_clk_tag(b, 3U);
        d17_set_timer_a_input_clk_TIMEOUT_TIMEBASE_1_MS(b,
                                                        v.TIMEOUT_TIMEBASE_1_MS);
    } else if (v.tag == TAG_ENUM_TIMEOUT_TIMEBASE_10_US) {
        d13_set_timer_a_input_clk_tag(b, 1U);
        d16_set_timer_a_input_clk_TIMEOUT_TIMEBASE_10_US(b,
                                                         v.TIMEOUT_TIMEBASE_10_US);
    } else {
        d13_set_timer_a_input_clk_tag(b, 2U);
        d15_set_timer_a_input_clk_TIMEOUT_TIMEBASE_100_US(b,
                                                          v.TIMEOUT_TIMEBASE_100_US);
    }
}
static inline void d21_set_timer_e_input_clk_tag_part0(t3 *b, unsigned int v)
{
    (*b).data[0U] = ((*b).data[0U] & ~(0X7U << 0U)) | (0X7U & v) << 0U;
}
static inline void d20_set_timer_e_input_clk_tag(t3 *b, unsigned int v)
{
    d21_set_timer_e_input_clk_tag_part0(b, (unsigned int) (v >> 0U & 7U));
}
static inline void d22_set_timer_e_input_clk_TIMESTAMP_TIMEBASE_100_US(t3 *b,
                                                                       unit_t v)
{ }
static inline void d23_set_timer_e_input_clk_TIMESTAMP_TIMEBASE_10_US(t3 *b,
                                                                      unit_t v)
{ }
static inline void d24_set_timer_e_input_clk_TIMESTAMP_TIMEBASE_1_MS(t3 *b,
                                                                     unit_t v)
{ }
static inline void d25_set_timer_e_input_clk_TIMESTAMP_TIMEBASE_1_US(t3 *b,
                                                                     unit_t v)
{ }
static inline void d26_set_timer_e_input_clk_TIMESTAMP_TIMEBASE_SYSTEM(t3 *b,
                                                                       unit_t v)
{ }
static inline void d19_set_timer_e_input_clk(t3 *b, t2 v)
{
    if (v.tag == TAG_ENUM_TIMESTAMP_TIMEBASE_SYSTEM) {
        d20_set_timer_e_input_clk_tag(b, 0U);
        d26_set_timer_e_input_clk_TIMESTAMP_TIMEBASE_SYSTEM(b,
                                                            v.TIMESTAMP_TIMEBASE_SYSTEM);
    } else if (v.tag == TAG_ENUM_TIMESTAMP_TIMEBASE_1_US) {
        d20_set_timer_e_input_clk_tag(b, 1U);
        d25_set_timer_e_input_clk_TIMESTAMP_TIMEBASE_1_US(b,
                                                          v.TIMESTAMP_TIMEBASE_1_US);
    } else if (v.tag == TAG_ENUM_TIMESTAMP_TIMEBASE_1_MS) {
        d20_set_timer_e_input_clk_tag(b, 4U);
        d24_set_timer_e_input_clk_TIMESTAMP_TIMEBASE_1_MS(b,
                                                          v.TIMESTAMP_TIMEBASE_1_MS);
    } else if (v.tag == TAG_ENUM_TIMESTAMP_TIMEBASE_10_US) {
        d20_set_timer_e_input_clk_tag(b, 2U);
        d23_set_timer_e_input_clk_TIMESTAMP_TIMEBASE_10_US(b,
                                                           v.TIMESTAMP_TIMEBASE_10_US);
    } else {
        d20_set_timer_e_input_clk_tag(b, 3U);
        d22_set_timer_e_input_clk_TIMESTAMP_TIMEBASE_100_US(b,
                                                            v.TIMESTAMP_TIMEBASE_100_US);
    }
}
static inline void d29_set_timer_a_mode_part0(t3 *b, unsigned int v)
{
    (*b).data[0U] = ((*b).data[0U] & ~(0X1U << 11U)) | (0X1U & v) << 11U;
}
static inline void d28_set_timer_a_mode(t3 *b, bool_t v)
{
    d29_set_timer_a_mode_part0(b, (unsigned int) (v.boolean >> 0U & 1U));
}
static inline void d31_set_timer_a_part0(t3 *b, unsigned int v)
{
    (*b).data[1U] = ((*b).data[1U] & ~(0XFFFFFFFFU << 0U)) | (0XFFFFFFFFU &
                                                              v) << 0U;
}
static inline void d30_set_timer_a(t3 *b, u32 v)
{
    d31_set_timer_a_part0(b, (unsigned int) (v >> 0U & 4294967295U));
}
static inline void d33_set_timer_a_en_part0(t3 *b, unsigned int v)
{
    (*b).data[0U] = ((*b).data[0U] & ~(0X1U << 15U)) | (0X1U & v) << 15U;
}
static inline void d32_set_timer_a_en(t3 *b, bool_t v)
{
    d33_set_timer_a_en_part0(b, (unsigned int) (v.boolean >> 0U & 1U));
}
static inline unsigned int d35_get_timer_a_en_part0(t3 *b)
{
    return (*b).data[0U] >> 15U & 0X1U;
}
static inline bool_t d34_get_timer_a_en(t3 *b)
{
    return (bool_t) {.boolean = (unsigned char) d35_get_timer_a_en_part0(b) <<
                     0U};
}
static inline unsigned int d37_get_timer_a_part0(t3 *b)
{
    return (*b).data[1U] >> 0U & 0XFFFFFFFFU;
}
static inline u32 d36_get_timer_a(t3 *b)
{
    return (u32) d37_get_timer_a_part0(b) << 0U;
}
static inline unsigned int d39_get_timer_a_mode_part0(t3 *b)
{
    return (*b).data[0U] >> 11U & 0X1U;
}
static inline bool_t d38_get_timer_a_mode(t3 *b)
{
    return (bool_t) {.boolean = (unsigned char) d39_get_timer_a_mode_part0(b) <<
                     0U};
}
static inline unsigned int d42_get_timer_a_input_clk_tag_part0(t3 *b)
{
    return (*b).data[0U] >> 8U & 0X3U;
}
static inline unsigned int d41_get_timer_a_input_clk_tag(t3 *b)
{
    return (unsigned int) d42_get_timer_a_input_clk_tag_part0(b) << 0U;
}
static inline unit_t d43_get_timer_a_input_clk_TIMEOUT_TIMEBASE_100_US(t3 *b)
{
    return (unit_t) {.dummy = 0};
}
static inline unit_t d44_get_timer_a_input_clk_TIMEOUT_TIMEBASE_10_US(t3 *b)
{
    return (unit_t) {.dummy = 0};
}
static inline unit_t d45_get_timer_a_input_clk_TIMEOUT_TIMEBASE_1_MS(t3 *b)
{
    return (unit_t) {.dummy = 0};
}
static inline unit_t d46_get_timer_a_input_clk_TIMEOUT_TIMEBASE_1_US(t3 *b)
{
    return (unit_t) {.dummy = 0};
}
static inline t1 d40_get_timer_a_input_clk(t3 *b)
{
    return d41_get_timer_a_input_clk_tag(b) == 0U ? (t1) {.tag =
                                                          TAG_ENUM_TIMEOUT_TIMEBASE_1_US,
                                                          .TIMEOUT_TIMEBASE_1_US =
                                                          d46_get_timer_a_input_clk_TIMEOUT_TIMEBASE_1_US(b)} : d41_get_timer_a_input_clk_tag(b) ==
        3U ? (t1) {.tag = TAG_ENUM_TIMEOUT_TIMEBASE_1_MS,
                   .TIMEOUT_TIMEBASE_1_MS =
                   d45_get_timer_a_input_clk_TIMEOUT_TIMEBASE_1_MS(b)} : d41_get_timer_a_input_clk_tag(b) ==
        1U ? (t1) {.tag = TAG_ENUM_TIMEOUT_TIMEBASE_10_US,
                   .TIMEOUT_TIMEBASE_10_US =
                   d44_get_timer_a_input_clk_TIMEOUT_TIMEBASE_10_US(b)} : (t1) {.tag =
                                                                                TAG_ENUM_TIMEOUT_TIMEBASE_100_US,
                                                                                .TIMEOUT_TIMEBASE_100_US =
                                                                                d43_get_timer_a_input_clk_TIMEOUT_TIMEBASE_100_US(b)};
}
static inline unsigned int d49_get_timer_e_input_clk_tag_part0(t3 *b)
{
    return (*b).data[0U] >> 0U & 0X7U;
}
static inline unsigned int d48_get_timer_e_input_clk_tag(t3 *b)
{
    return (unsigned int) d49_get_timer_e_input_clk_tag_part0(b) << 0U;
}
static inline unit_t d50_get_timer_e_input_clk_TIMESTAMP_TIMEBASE_100_US(t3 *b)
{
    return (unit_t) {.dummy = 0};
}
static inline unit_t d51_get_timer_e_input_clk_TIMESTAMP_TIMEBASE_10_US(t3 *b)
{
    return (unit_t) {.dummy = 0};
}
static inline unit_t d52_get_timer_e_input_clk_TIMESTAMP_TIMEBASE_1_MS(t3 *b)
{
    return (unit_t) {.dummy = 0};
}
static inline unit_t d53_get_timer_e_input_clk_TIMESTAMP_TIMEBASE_1_US(t3 *b)
{
    return (unit_t) {.dummy = 0};
}
static inline unit_t d54_get_timer_e_input_clk_TIMESTAMP_TIMEBASE_SYSTEM(t3 *b)
{
    return (unit_t) {.dummy = 0};
}
static inline t2 d47_get_timer_e_input_clk(t3 *b)
{
    return d48_get_timer_e_input_clk_tag(b) == 0U ? (t2) {.tag =
                                                          TAG_ENUM_TIMESTAMP_TIMEBASE_SYSTEM,
                                                          .TIMESTAMP_TIMEBASE_SYSTEM =
                                                          d54_get_timer_e_input_clk_TIMESTAMP_TIMEBASE_SYSTEM(b)} : d48_get_timer_e_input_clk_tag(b) ==
        1U ? (t2) {.tag = TAG_ENUM_TIMESTAMP_TIMEBASE_1_US,
                   .TIMESTAMP_TIMEBASE_1_US =
                   d53_get_timer_e_input_clk_TIMESTAMP_TIMEBASE_1_US(b)} : d48_get_timer_e_input_clk_tag(b) ==
        4U ? (t2) {.tag = TAG_ENUM_TIMESTAMP_TIMEBASE_1_MS,
                   .TIMESTAMP_TIMEBASE_1_MS =
                   d52_get_timer_e_input_clk_TIMESTAMP_TIMEBASE_1_MS(b)} : d48_get_timer_e_input_clk_tag(b) ==
        2U ? (t2) {.tag = TAG_ENUM_TIMESTAMP_TIMEBASE_10_US,
                   .TIMESTAMP_TIMEBASE_10_US =
                   d51_get_timer_e_input_clk_TIMESTAMP_TIMEBASE_10_US(b)} : (t2) {.tag =
                                                                                  TAG_ENUM_TIMESTAMP_TIMEBASE_100_US,
                                                                                  .TIMESTAMP_TIMEBASE_100_US =
                                                                                  d50_get_timer_e_input_clk_TIMESTAMP_TIMEBASE_100_US(b)};
}
static inline void d56_set_timer_e_hi_part0(t3 *b, unsigned int v)
{
    (*b).data[19U] = ((*b).data[19U] & ~(0XFFFFFFFFU << 0U)) | (0XFFFFFFFFU &
                                                                v) << 0U;
}
static inline void d55_set_timer_e_hi(t3 *b, u32 v)
{
    d56_set_timer_e_hi_part0(b, (unsigned int) (v >> 0U & 4294967295U));
}
static inline t3 *reset_timer_e_cogent(t3 *a1)
{
    t3 *r2 = a1;
    u32 r3 = 0U;
    t3 *r4 = r2;
    
    d4_set_timer_e(r4, r3);
    
    t3 *r5 = r4;
    
    return r5;
}
static inline u64 meson_get_time(t6 *a1)
{
    t6 *r2 = a1;
    t3 *r3 = (*r2).regs;
    u32 r4 = d7_get_timer_e_hi(r3);
    u64 r5 = (u64) r4;
    t3 *r6 = (*r2).regs;
    u32 r7 = d9_get_timer_e(r6);
    u64 r8 = (u64) r7;
    t3 *r9 = (*r2).regs;
    u32 r10 = d7_get_timer_e_hi(r9);
    u64 r11 = (u64) r10;
    bool_t r12 = (bool_t) {.boolean = r11 != r5};
    u64 r13;
    
    if (r12.boolean) {
        t3 *r14 = (*r2).regs;
        u32 r15 = d9_get_timer_e(r14);
        u64 r16 = (u64) r15;
        u64 r17 = 32U;
        u64 r18 = r17 >= 64U ? 0U : r11 << r17;
        u64 r19 = r18 | r16;
        u64 r20 = 1000U;
        u64 r21 = r19 * r20;
        
        r13 = r21;
    } else {
        u64 r22 = r8;
        u64 r23 = 32U;
        u64 r24 = r23 >= 64U ? 0U : r11 << r23;
        u64 r25 = r24 | r22;
        u64 r26 = 1000U;
        u64 r27 = r25 * r26;
        
        r13 = r27;
    }
    
    u64 r28 = r13;
    
    return r28;
}
static inline t6 *meson_init(t11 a1)
{
    t6 *r2 = a1.p1;
    VAddr *r3 = a1.p2;
    t3 *r4 = config_get_regs(r3);
    unit_t r5 = (unit_t) {.dummy = 0};
    t1 r6;
    
    r6 = (t1) {.tag = TAG_ENUM_TIMEOUT_TIMEBASE_1_MS, .TIMEOUT_TIMEBASE_1_MS =
               r5};
    
    t1 r7 = r6;
    t1 r8 = r7;
    t3 *r9 = r4;
    
    d12_set_timer_a_input_clk(r9, r8);
    
    t3 *r10 = r9;
    unit_t r11 = (unit_t) {.dummy = 0};
    t2 r12;
    
    r12 = (t2) {.tag = TAG_ENUM_TIMESTAMP_TIMEBASE_1_US,
                .TIMESTAMP_TIMEBASE_1_US = r11};
    
    t2 r13 = r12;
    t2 r14 = r13;
    t3 *r15 = r10;
    
    d19_set_timer_e_input_clk(r15, r14);
    
    t3 *r16 = r15;
    t3 *r17 = reset_timer_e(r16);
    t6 *r18 = r2;
    
    (*r18).regs = r17;
    
    t6 *r19 = r18;
    
    return r19;
}
static inline t6 *meson_set_timeout(t27 a1)
{
    t6 *r2 = a1.p1;
    u16 r3 = a1.p2;
    bool_t r4 = a1.p3;
    t3 *r5 = (*r2).regs;
    t3 *r6 = r5;
    
    d28_set_timer_a_mode(r6, r4);
    
    t3 *r7 = r6;
    u32 r8 = (u32) r3;
    t3 *r9 = r7;
    
    d30_set_timer_a(r9, r8);
    
    t3 *r10 = r9;
    bool_t r11;
    
    if (LETBANG_TRUE) {
        r11 = (*r2).disable;
    } else
        ;
    
    t6 *r12;
    
    if (r11.boolean) {
        bool_t r13 = (bool_t) {.boolean = 1U};
        t3 *r14 = r10;
        
        d32_set_timer_a_en(r14, r13);
        
        t3 *r15 = r14;
        t6 *r16 = r2;
        
        (*r16).regs = r15;
        
        t6 *r17 = r16;
        bool_t r18 = (bool_t) {.boolean = 0U};
        t6 *r19 = r17;
        
        (*r19).disable = r18;
        r12 = r19;
    } else {
        t6 *r20 = r2;
        
        (*r20).regs = r10;
        r12 = r20;
    }
    
    t6 *r21 = r12;
    
    return r21;
}
static inline t6 *meson_stop_timer(t6 *a1)
{
    t3 *r2 = (*a1).regs;
    bool_t r3 = (bool_t) {.boolean = 0U};
    t3 *r4 = r2;
    
    d32_set_timer_a_en(r4, r3);
    
    t3 *r5 = r4;
    t6 *r6 = a1;
    
    (*r6).regs = r5;
    
    t6 *r7 = r6;
    bool_t r8 = (bool_t) {.boolean = 1U};
    t6 *r9 = r7;
    
    (*r9).disable = r8;
    
    t6 *r10 = r9;
    
    return r10;
}

