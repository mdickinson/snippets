#include <stdio.h>
#include <inttypes.h>

uint16_t isqrt32(uint32_t x);
uint32_t isqrt64(uint64_t x);

// Check isqrt32 for a single input. Return 0 for success, 1 for failure.
// Also prints an error message on failure.

static int check_isqrt32(uint32_t x) {
    uint32_t y = isqrt32(x);
    int bad_isqrt = x < y*y || 2*y < x - y*y;
    if (bad_isqrt) {
        printf("isqrt32(%" PRIu32 ") returned incorrect answer %"
               PRIu32 "\n", x, y);
    }
    return bad_isqrt;
}

// Check isqrt64 for a single input. Return 0 for success, 1 for failure.
// Also prints an error message on failure.

static int check_isqrt64(uint64_t x) {
    uint64_t y = isqrt64(x);
    int bad_isqrt = x < y*y || 2*y < x - y*y;
    if (bad_isqrt) {
        printf("isqrt64(%" PRIu64 ") returned incorrect answer %"
               PRIu64 "\n", x, y);
    }
    return bad_isqrt;
}

// Check isqrt32 for all possible inputs. Return 0 for success, 1 for failure.

static int test_isqrt32(void)
{
    printf("Checking isqrt32 for all values in [0, 2**32) ...\n");
    uint32_t x = 0;
    do {
        if (check_isqrt32(x)) return 1;
    } while (++x);
    printf("All tests passed\n");
    return 0;
}

// Check isqrt64 for a selection of inputs. Return 0 for success, 1 for failure.

static int test_isqrt64(void)
{
    printf("Checking isqrt64 for selected values in [0, 2**64) ...\n");
    for (uint64_t s = 0; s < 0x100000000u; s++) {
        if (check_isqrt64(s*s)) return 1;
        if (check_isqrt64(s*s + s)) return 1;
        if (check_isqrt64(s*s + 2*s)) return 1;
    };
    printf("All tests passed\n");
    return 0;
}

// Main program: run 32-bit and 64-bit tests.

int main(void) {
    return (test_isqrt32() | test_isqrt64());
}
