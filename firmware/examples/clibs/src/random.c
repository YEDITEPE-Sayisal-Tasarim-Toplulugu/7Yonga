#include "random.h"

#include <stdint.h>

static volatile uint32_t random_seed = 0xACE1;

// by @chatGPT
uint32_t my_random(void)
{
    uint32_t bit = ((random_seed >> 0) ^ (random_seed >> 1) ^ (random_seed >> 3) ^ (random_seed >> 12)) & 1;
    random_seed = (random_seed >> 1) | (bit << 31);
    // return (random_seed != 0) ? random_seed : 0xACE1;
    return random_seed; // kontrol işini kullanıcıya bırak.
}

void srand(uint32_t new_seed)
{
    random_seed = new_seed;
}

uint32_t random(void)
{
    return my_random();
}

uint32_t random_m(int32_t max)
{
    return my_random() % max;
}

uint32_t random_mm(int32_t min, int32_t max)
{
    return my_random() % (max - min + 1) + min;
}