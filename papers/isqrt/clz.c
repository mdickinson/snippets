#include <assert.h>
#include <stdint.h>

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
