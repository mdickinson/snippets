"""
Generate and validate the lookup tables used in isqrt32.c and isqrt64.c.
"""

from math import isqrt

table0 = [isqrt(256*(k+65) - 1) for k in range(0, 192)]
table1 = [isqrt(256*(k+64) - 1) for k in range(0, 192)]

def check_tables():
    for t in range(2**14, 2**16):
        a = table0[(t>>8) - 64]      # isqrt64.c version
        b = 1 + table1[(t>>8) - 64]  # isqrt32.c version
        assert a <= b
        assert (a-1)*(a-1) < t < (a+1)*(a+1)
        assert (b-1)*(b-1) < t < (b+1)*(b+1)

def print_table(table, columns=10):
    for i in range(0, len(table0), columns):
        chunk = table[i:i+columns]
        print("    " + " ".join(f"{value}," for value in chunk))

check_tables()

print("Table for isqrt32_c")
print("===================")
print()
print("""\
// isqrt32_tab[k] = isqrt(256*(k+64)-1) for 0 <= k < 192
static const uint8_t isqrt32_tab[192] = {""")
print_table(table1)
print("};")
print()

print("Table for isqrt64_c")
print("===================")
print()
print("""\
// isqrt64_tab[k] = isqrt(256*(k+65)-1) for 0 <= k < 192
static const uint8_t isqrt64_tab[192] = {""")
print_table(table0)
print("};")
print()
