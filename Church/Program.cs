﻿using System;
using System.Collections.Generic;
using System.Linq;
using static Church;
using static System.Console;

class Program
{
	static void Main()
	{
		var time = DateTime.Now;
		var head = Leaf(2);
		head.Add(Leaf(1));
		head[0].Add(Leaf(3));
		head[0].Add(Leaf(0));
		head[0].Add(Leaf(2));
		head[0][0].Add(Leaf(0));
		head[0][0].Add(Leaf(2));
		head[0][2].Add(Leaf(4));
		head[0][2][0].Add(Leaf(1));
		var ct = head.ToCTree();
		var h2 = ToTree(ct);
		WriteLine(h2);
		/*for (var i = 0; i <= 6; i++) WriteLine($"{i} : {ToInt(fact(ToChurch(i)))}");
		for (var i = 0; i <= 3; i++) WriteLine($"{i} : {ToInt(nthPrime(ToChurch(i)))}");
		WriteLine(ToInt(lcm(ToChurch(16))(ToChurch(12))));
		WriteLine(ToInt(lcm(ToChurch(29))(ToChurch(4))));
		WriteLine(ToInt(lcm(ToChurch(18))(ToChurch(27))));
		WriteLine(ToInt(lcm(ToChurch(0))(ToChurch(5))));
		WriteLine(ToInt(lcm(ToChurch(32))(ToChurch(4))));*/
		var L = new List<int> { 3, 1, 4, 1, 5, 9 };
		//var L = new List<int> { 3 };
		var z = L.Select(ToCInt).ToList().ToCList();
		var w = ToList(z);
		WriteLine($"len = {ToInt(len(z))}, sum = {ToInt(sum(z))}, [{string.Join(", ", w.Select(ToInt))}]");
		WriteLine($"{3} : {ToInt(nthPrime(ToCInt(4)))}");
		WriteLine($"{3} : {ToInt(nthPrime(ToCInt(4)))}");
		WriteLine((DateTime.Now - time).TotalSeconds);
	}
}
static class Church
{
	public delegate Fun Fun(Fun f);

	// コンビネータ
	// S(x)(y)(z) -> x(z)(y(z))
	public static Fun S = x => y => z => x(z)(y(z));
	// K(x)(y) -> x
	public static Fun K = x => y => x;
	// I(x) -> x
	public static Fun I = x => x;
	// iota(x) -> x(S)(K)
	public static Fun iota = x => x(S)(K);
	// 不動点演算子
	// Y(f) は f(Y(f)) -> Y(f) を満たす
	public static Fun Y = f => ((Fun)(x => f(x(x))))(y => f(a => y(b => y(b))(a)));

	// 真偽値
	// True(a)(b) -> a
	public static Fun True = a => b => a;
	// False(a)(b) -> b
	public static Fun False = a => b => b;
	// If(True)(a)(b) -> a
	// If(False)(a)(b) -> b
	public static Fun If = p => a => b => p(a)(b);
	// and(a)(b) -> a&b
	public static Fun and = p => q => p(q)(False);
	// or(a)(b) -> a|b
	public static Fun or = p => q => p(True)(q);
	// xor(a)(b) -> a^b
	public static Fun xor = p => q => p(not(q))(q);
	// not(a) -> !a
	public static Fun not = p => p(False)(True);
	// 変換
	public static bool ToBool(Fun p) => p(True)(False) == True;
	public static Fun ToCBool(bool f) => f ? True : False;

	// 自然数
	// zero = 0
	public static Fun zero = f => x => x;
	// one = 1
	public static Fun one = f => x => f(x);
	// two = 2
	public static Fun two = f => x => f(f(x));
	// three = 3
	public static Fun three = f => x => f(f(f(x)));
	// succ(n) -> n+1
	public static Fun succ = n => f => x => f(n(f)(x));
	// pred(0) -> 0
	// pred(n+1) -> n
	public static Fun pred = n => f => x => n(g => h => h(g(f)))(K(x))(I);
	// mult(n)(m) -> n*m
	public static Fun mult = n => m => f => m(n(f));
	// add(n)(m) -> n+m
	public static Fun add = n => m => f => x => m(f)(n(f)(x));
	// pow(n)(m) -> n^m
	public static Fun pow = n => m => m(n);
	// sub(m)(n) -> m-n (m>=n)
	// sub(m)(n) -> 0 (m<n)
	public static Fun sub = m => n => n(pred)(m);
	// is0(n) -> n==0
	public static Fun is0 = n => n(K(False))(True);
	// leq(m)(n) -> m<=n
	public static Fun leq = m => n => is0(sub(m)(n));
	// geq(m)(n) -> m>=n
	public static Fun geq = m => n => is0(sub(n)(m));
	// eq(m)(n) -> m==n
	public static Fun eq = m => n => and(leq(m)(n))(leq(n)(m));
	// 変換
	static List<Fun> numerals;
	static Church() => numerals = new List<Fun> { zero, one, two, three };
	public static Fun ToCInt(int n)
	{
		for (var i = numerals.Count; i <= n; i++) numerals.Add(succ(numerals[i - 1]));
		return numerals[n];
	}
	public static int ToInt(Fun n)
	{
		var c = 0;
		n(x => { c++; return x; })(null);
		return c;
	}
	
	// タプル
	// pair(a)(b) -> (a, b)
	public static Fun pair = x => y => z => z(x)(y);
	// first((a, b)) -> a
	public static Fun first = x => x(True);
	// second((a, b)) -> b
	public static Fun second = x => x(False);
	// 変換
	public static (Fun x, Fun y) ToTuple(Fun a) => (first(a), second(a));
	public static Fun ToCTuple((Fun x, Fun y) a) => pair(a.x)(a.y);

	// 連結リスト
	// nil -> []
	public static Fun nil = False;
	// isnil(L) -> L==[]
	public static Fun isnil = l => l(K(K(False)))(True);
	// consl(t)(L) -> [t, L]
	public static Fun consl = h => t => c => n => t(c)(c(n)(h));
	// consr(t)(L) -> [L, t]
	public static Fun consr = h => t => c => n => c(t(c)(n))(h);
	// head([]) -> nil
	// head([t, L]) -> t
	public static Fun head = l => second(l(x => y => pair(False)(first(x)(y)(second(x))))(pair(True)(nil)));
	// tail([]) -> nil
	// tail([t, L]) -> L
	public static Fun tail = l => second(l(p => x => pair(False)(first(p)(False)(consr(x)(second(p)))))(pair(True)(nil)));
	// len(L) -> length of L
	public static Fun len = l => l(a => succ)(zero);
	// sum(L) -> sum of L
	public static Fun sum = l => l(add)(zero);
	// lmax([]) -> 0
	// lmax(L) -> max value of L
	public static Fun lmax = l => l(max)(zero);
	// lmin([]) -> 0
	// lmin(L) -> min value of L
	public static Fun lmin = l => isnil(l)(zero)(tail(l)(min)(head(l)));
	// 変換
	public static List<Fun> ToList(Fun z)
	{
		var list = new List<Fun>();
		z(x => y => { list.Add(y); return x; })(nil);
		return list;
	}
	public static Fun ToCList(this IList<Fun> z)
	{
		var L = nil;
		foreach (var x in z) L = consr(x)(L);
		return L;
	}

	// より高度な自然数上の関数
	// f(0) = z
	// f(n+1) = next(f(x))(x+1)
	public static Fun rec(Fun z, Fun next) => Y(f => x => is0(x)(t => z(t))(t => next(f(pred(x)))(x)(t)));
	// fact(n) = n!
	public static Fun fact = rec(one, prev => x => mult(x)(prev));
	// max(m)(n) = max(m, n)
	public static Fun max = n => m => leq(n)(m)(m)(n);
	// min(m)(n) = min(m, n)
	public static Fun min = n => m => leq(n)(m)(n)(m);
	// div(m)(0) = m
	// div(m)(n) = m/n
	public static Fun div = n => m => is0(m)(n) // if m==0 then n
		(Y(f => x =>    // x = (n, m) and f(x) = n / m
			leq(succ(first(x)))(second(x))  // if n+1 <= m i.e. n < m
				(zero)  // then 0
				(t => succ(f(pair(sub(first(x))(second(x)))(second(x))))(t)))   // else f(x) = 1 + f((n - m, m))
			(pair(n)(m)));
	// mod(m)(0) = m
	// mod(m)(n) = m%n
	public static Fun mod = n => m => is0(m)(n) // if m==0 then n
		(Y(f => x =>    // x = (n, m) and f(x) = n % m
			leq(succ(first(x)))(second(x))  // if n+1 <= m 
				(t => first(x)(t))  // then n
				(t => f(pair(sub(first(x))(second(x)))(second(x)))(t)))   // else f(x) = f((n - m, m))
			(pair(n)(m)));
	// isPrime(n) = n is a prime number
	public static Fun isPrime = n => and(leq(succ(succ(zero)))(n))(
		Y(f => x => // x = (i, n) and f(x) = And(n % j > 0, 2 <= j <= i)
			  leq(second(x))(first(x))  // if i >= n
				  (True)    // then true
				  (t => and(s => leq(succ(zero))(mod(second(x))(first(x)))(s))(s => f(pair(succ(first(x)))(second(x)))(s))(t))  // else f(i+1, n) & (n%i >= 1)
		)(pair(two)(n)));
	// nthPrime(0) = 2, (1) = 3, (2) = 5, (3) = 7, ...
	public static Fun nthPrime = rec(two, p => _ => Y(f => x =>    // f(x) = min(p, p >= x & p is prime)
		isPrime(x)(t => x(t))(t => f(succ(x))(t))
	)(succ(p)));
	// gcd(m)(n) = gcd(m, n)
	public static Fun gcd = n => m => Y(f => x =>   // x = (n, m), f(x) = gcd(n, m)
		is0(first(x))   // if n == 0
			(t => second(x)(t)) // then m
			(t => f(pair(mod(second(x))(first(x)))(first(x)))(t))   // else f((m%n, n))
	)(pair(n)(m));
	// lcm(m)(n) = lcm(m, n)
	public static Fun lcm = n => m => mult(div(n)(gcd(n)(m)))(m);

	// 根付き木
	public static Fun tree = n => ch => pair(n)(ch);
	public static Tree Leaf(int n) => new Tree(ToCInt(n));
	public class Tree
	{
		public Fun node;
		public List<Tree> children = new List<Tree>();
		public Tree this[int n] { get { return children[n]; } set { children[n] = value; } }
		public Tree(Fun node) => this.node = node;
		public void Add(Tree t) => children.Add(t);
		public Fun ToCTree()
		{
			var ch = children.Select(x => x.ToCTree()).ToList();
			return tree(node)(ToCList(ch));
		}
		public override string ToString()
		{
			var s = ToInt(node).ToString();
			if (children.Count > 0) s += "[" + string.Join(", ", children.Select(x => x.ToString())) + "]";
			return s;
		}
	}
	public static Tree ToTree(Fun t)
	{
		var head = new Tree(first(t));
		second(t)(x => y => { head.children.Add(ToTree(y)); return y; })(null);
		return head;
	}
}
