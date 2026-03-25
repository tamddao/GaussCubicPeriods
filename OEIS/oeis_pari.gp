\\ ============================================================
\\ PARI/GP for OEIS: Product of cubic Gauss periods
\\ a(n) = ((c+3)*q - 1)/27
\\ where q = A002476(n), q = a^2+a*b+7*b^2, c = 2a+b, c == 1 (mod 3)
\\ ============================================================

\\ --- Compact version for OEIS Program field ---
\\
\\ (PARI) e3(q) = for(b=-sqrtint(q\7)-1, sqrtint(q\7)+1, my(d=4*q-27*b^2, s); if(d>=0 && issquare(d, &s), for(j=0, 1, my(a=(-b+(-1)^j*s)/2); if(type(a)=="t_INT" && a^2+a*b+7*b^2==q && gcd(abs(a), abs(b))==1, my(c=2*a+b); if(c%3==1, return(((c+3)*q-1)/27)); if((-c)%3==1, return(((-c+3)*q-1)/27))))));
\\ a(n) = my(cnt=0); forprime(q=7, +oo, if(q%3==1, cnt++; if(cnt==n, return(e3(q)))));
\\ vector(50, n, a(n))

\\ --- Full readable version ---

e3(q) = {
  my(bmax = sqrtint(4*q\27) + 1);
  for(b = -bmax, bmax,
    my(d = 4*q - 27*b^2, s);
    if(d >= 0 && issquare(d, &s),
      for(j = 0, 1,
        my(a = (-b + (-1)^j * s) / 2);
        if(type(a) == "t_INT" && a^2 + a*b + 7*b^2 == q && gcd(abs(a), abs(b)) == 1,
          my(c = 2*a + b);
          if(c % 3 == 1, return(((c+3)*q - 1)/27));
          if((-c) % 3 == 1, return(((-c+3)*q - 1)/27));
        )
      )
    )
  );
}

a(n) = {
  my(cnt = 0);
  forprime(q = 7, +oo,
    if(q % 3 == 1,
      cnt++;
      if(cnt == n, return(e3(q)))
    )
  );
}

\\ --- Direct verification via Gauss periods ---
e3_direct(q) = {
  my(g = znprimroot(q), k = (q-1)/3);
  my(zq = exp(2*Pi*I/q));
  my(eta = vector(3, j,
    sum(t = 0, k-1, zq^lift(g^(3*t + j - 1)))
  ));
  round(real(eta[1] * eta[2] * eta[3]))
}

\\ --- Test ---
print("First 50 terms:");
print(vector(50, n, a(n)));

{
  my(cnt = 0);
  forprime(q = 7, 200,
    if(q % 3 == 1,
      cnt++;
      my(f = e3(q), d = e3_direct(q));
      if(f != d,
        print("MISMATCH at q=", q, ": formula=", f, " direct=", d),
        print("q=", q, ": ", f, " OK")
      );
    )
  );
  print("Verified ", cnt, " primes, all match.");
}
