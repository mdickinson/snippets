#include <assert.h>
#include <stdio.h>

#include "isqrt32.c"

static const uint8_t clz32_tab[32] =
{
    31, 22, 30, 21, 18, 10, 29,  2, 20, 17, 15, 13, 9,  6, 28, 1,
    23, 19, 11,  3, 16, 14,  7, 24, 12,  4,  8, 25, 5, 26, 27, 0
};

// count leading zeros of nonzero 32-bit unsigned integer
// See https://graphics.stanford.edu/~seander/bithacks.html#IntegerLogDeBruijn.
int clz32(uint32_t x)
{
    assert(x);
    x |= x >> 1;
    x |= x >> 2;
    x |= x >> 4;
    x |= x >> 8;
    x |= x >> 16;
    return clz32_tab[(uint32_t)(x * 0x07c4acddu) >> 27];
}

int check_isqrt32(uint32_t x) {
    uint32_t y = isqrt32(x);
    int y_ok = y*y <= x && x - y*y <= 2*y;
    if (!y_ok) {
        printf("isqrt32(%u) returned incorrect answer %u\n", x, y);
    }
    return y_ok;
}

int main(void)
{
    printf("Checking isqrt32 for all values in [0, 2**32) ...\n");
    uint32_t x = 0;
    do {
        if (!check_isqrt32(x)) return 1;
    } while (++x);
    printf("All tests passed\n");
    return 0;
}
