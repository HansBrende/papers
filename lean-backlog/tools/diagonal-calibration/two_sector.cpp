#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <vector>

// Exact GF(2) enumeration of two covariant displacement sectors.
// It proves nothing about three or more coupled sectors or noncovariant codes.
using Rows = std::array<uint32_t, 32>;
using Block = std::array<uint32_t, 16>;

int rank_at_most(Rows rows, int stop) {
    std::array<uint32_t, 32> pivots{};
    int r = 0;
    for (uint32_t x : rows) {
        while (x) {
            int k = __builtin_ctz(x);
            if (pivots[k]) x ^= pivots[k];
            else {
                pivots[k] = x;
                if (++r > stop) return r;
                break;
            }
        }
    }
    return r;
}

std::array<Block, 32> blocks(int h) {
    const int T[] = {1, 2, 4, 8, 15};
    std::array<Block, 32> out{};
    for (int m = 0; m < 32; ++m)
        for (int x = 0; x < 16; ++x)
            for (int t = 0; t < 5; ++t)
                if ((m >> t) & 1) out[m][x] ^= 1u << (x ^ h ^ T[t]);
    return out;
}

int main() {
    const int pairs[][2] = {{0, 3}, {3, 5}, {3, 12}};
    for (const auto &pair : pairs) {
        int g = pair[0], h = pair[1];
        auto G = blocks(g), H = blocks(h);
        int rg = 16, rh = 16;
        for (int m = 0; m < 32; ++m) {
            Rows a{}, b{};
            for (int x = 0; x < 16; ++x) {
                a[x] = G[m][x] ^ (1u << x);
                b[x] = H[m][x] ^ (1u << x);
            }
            rg = std::min(rg, rank_at_most(a, 32));
            rh = std::min(rh, rank_at_most(b, 32));
        }
        const int baseline = rg + rh;
        assert(baseline == (g == 0 ? 10 : 8));
        unsigned count = 0;
        bool found = false;
        for (int a = 0; a < 32 && !found; ++a)
        for (int b = 0; b < 32 && !found; ++b)
        for (int c = 0; c < 32 && !found; ++c)
        for (int d = 0; d < 32 && !found; ++d) {
            Rows R{};
            for (int x = 0; x < 16; ++x) {
                R[x] = (G[a][x] ^ (1u << x)) | (H[b][x] << 16);
                R[16+x] = G[c][x] | ((H[d][x] ^ (1u << x)) << 16);
            }
            ++count;
            int rank = rank_at_most(R, baseline - 1);
            if (rank < baseline) {
                printf("FOUND g=%d h=%d masks=%d,%d,%d,%d rank=%d baseline=%d count=%u\n",
                    g,h,a,b,c,d,rank,baseline,count);
                for (auto row : R) printf("%u ",row);
                puts("");
                found = true;
            }
        }
        if (!found) assert(count == (1u << 20));
        printf("DONE g=%d h=%d tested=%u baseline=%d gain=%s\n",
            g,h,count,baseline,found?"yes":"no");
        fflush(stdout);
    }
}
