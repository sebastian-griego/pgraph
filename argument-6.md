# Argument, part 6

Let P be any n-point set with at most h hull vertices. Using the fixed-edge input, part 3, and part 5,

pg(P) >= g_{b_n}(P)
      >= g_{a_n}(P) binom(L_n,b_n) / binom(L_n,a_n)
      >= binom(n,s_n) * 1/(d_n+1) * binom(n-3,d_n) * binom(n+d_n-1,d_n)
         * binom(L_n,b_n) / binom(L_n,a_n).              (5)

The right side depends only on n and h, so it also lower-bounds m_h(n).
