#include <assert.h>
#include <stdio.h>

#include "isqrt64.c"

static const uint8_t clz64_tab[64] = {
    63,  5, 62,  4, 16, 10, 61,  3, 24, 15, 36,  9, 30, 21, 60,  2,
    12, 26, 23, 14, 45, 35, 43,  8, 33, 29, 52, 20, 49, 41, 59,  1,
     6, 17, 11, 25, 37, 31, 22, 13, 27, 46, 44, 34, 53, 50, 42,  7,
    18, 38, 32, 28, 47, 54, 51, 19, 39, 48, 55, 40, 56, 57, 58,  0,
};

// count leading zeros of nonzero 64-bit unsigned integer. Analogous to the
// 32-bit version at
// https://graphics.stanford.edu/~seander/bithacks.html#IntegerLogDeBruijn.
int clz64(uint64_t x)
{
    assert(x);
    x |= x >> 1;
    x |= x >> 2;
    x |= x >> 4;
    x |= x >> 8;
    x |= x >> 16;
    x |= x >> 32;
    return clz64_tab[(uint64_t)(x * 0x03f6eaf2cd271461u) >> 58];
}

int check_isqrt64(uint64_t x) {
    uint64_t y = isqrt64(x);
    int y_ok = y*y <= x && x - y*y <= 2*y;
    if (!y_ok) {
        printf("isqrt64(%llu) returned incorrect answer %llu\n", x, y);
    }
    return y_ok;
}

int main(void)
{
    printf("Checking isqrt64 for selected values in [0, 2**64) ...\n");
    for (uint64_t s = 0; s < 0x100000000u; s++) {
        if (!check_isqrt64(s*s)) return 1;
        if (!check_isqrt64(s*s + s)) return 1;
        if (!check_isqrt64(s*s + 2*s)) return 1;
    };
    printf("All tests passed\n");
    return 0;
}
