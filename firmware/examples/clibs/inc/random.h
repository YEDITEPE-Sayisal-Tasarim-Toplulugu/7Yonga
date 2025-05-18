#ifndef __RANDOM_H__
#define __RANDOM_H__

#include <stdint.h>

uint32_t my_random(void);
void srand(uint32_t new_seed);
uint32_t random(void);
uint32_t random_m(int32_t max);
uint32_t random_mm(int32_t min, int32_t max);

#endif // __RANDOM_H__