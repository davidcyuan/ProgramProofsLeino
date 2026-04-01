method MyMethod(x: int) returns (y: int)
  requires 10 <= x
  ensures 25 <= y
{
  var a, b;
  a := x + 3;
  if x < 20 {
    b := 32 - x;
  }
  else {
    b := 16;
  }
  y := a + b;
}

// Exercise 2.0
method MyMethod_two_point_zero(x: int) returns (y: int)
  requires x == 18
  ensures 25 <= y
{
  var a, b;
  a := x + 3;
  if x < 20 {
    b := 32 - x;
  }
  else {
    b := 16;
  }
  y := a + b;

  // program state at (9)
  assert a == 21;
  assert b == 14;
  assert y == 35;

  // program state (10)
  // y == 35;
}

// Exercise 2.1
/* Prove 10 <= x && a == x + 3 && b == 12 && y == a + b ==> 25 <= y
  is a valid formula, aka a formula that evaluates to true for any values
  10 <= a - 3 ==> 13 <= a
  13 + 12 <= a + b == y
  25 <= y
*/

// Exercise 2.2
/* Prove 10 <= x ==> 25 <= x + 3 + 12
  25 <= x + 15 == x + 3 + 12
*/

// Hoare Triple: {{P}} S {{Q}}
// if S is started in a state satisfying P, then S will terminate in a state satisfying Q

// Exercise 2.3
/*  a) Prove {{ x== y }} z := x - y {{ z == 0 }}
      z == 0;
    b) {{ true }} x := 100 {{ x == 100 }}
      x == 100;
    c) {{ true }} x := 2 * y {{ x is even }}
      x % 2 == 0;
    d) {{ x == 89 }} y := x - 34 {{ x == 89 }}
      x == 89;
    e) {{ x == 3 }} x := x + 1 {{ x == 4 }}
      x == 4;
    f) {{ 0 <= x < 100 }} x := x + 1 {{ 0 < x <= 100 }}
      1 < x + 1 < 101
      0 < 1 < x + 1
      x + 1 < 101 ==> x + 1 <= 100 (only if x is an integer)
*/

module Exercise_2_4 {
// Find initial values of x and y st. the triple does NOT hold

  /* a) {{ true }} x := 2 * y {{ y <= x }}
    y := -1
    x == -2
    -1 > -2
  */
  method A()
  {
    var y := -1;
    var x := 2 * y;
    assert (y <= x);
  }

  /* b) {{ x == 3 }} x := x + 1 {{ y == 4 }}
    y := 1
    1 != 4
  */
  method B()
  {
    var x := 3;
    var y := 1;

    x := x + 1;
    assert y == 4;
  }

  /* c) {{ true }} x := 100 {{ false }}
    false
  */
  method C()
  {
    var x := 100;
    assert false;
  }

  /* d) {{ 0 <= x }} x := x - 1 {{ 0 <= x }}
    x := 0
    x - 1 == -1
    0 > -1
  */
  method D()
  {
    var x := 0;
    
    x := x - 1;
    assert 0 <= x;
  }
}

module Exercise_2_5 {
// Come up with predicate, as precise as possible, st. the Hoare triple holds

  /* a) {{ 0 <= x }} x := 2 * x {{ ? }}
    0 <= 2 * x
    0 <= x
  */
  method A(x: int)
    requires 0 <= x
  {
    var x' := 2 * x;

    assert 0 <= x';
  }
  
  /* b) {{ 0 <= x <= y < 100 }} z := y - x {{ ? }}
    -x <= 0 <= y - x < 100 - x
    -x <= 0 <= z < 100 - x
    0 <= z < 100 - x
  */
  method B(x: int, y: int)
    requires 0 <= x <= y < 100
  {
    var z := y - x;

    assert 0 <= z < 100 - x;
  }

  /* c) {{ 0 <= x < N }} x := x + 1 {{ ? }}
    1 <= x + 1 < N + 1
    1 <= x <= N
  */
  method C(x: int, N: int)
    requires 0 <= x < N
  {
    var x' := x + 1;

    assert 1 <= x' <= N;
  }
  
}

module Exercise_2_6 {
// Come up with predicate, as precise as possible, st. the Hoare triple holds

  method A(x: int) 
    requires -128 <= x < 0
  {
    var x' := 1 - x;
    /*
      128 >= -x > 0
      129 >= 1 - x > 1
      129 >= x' > 1
    */

    assert 1 < x' <= 129;
  }

  method B(x: int, y: int)
    requires 0 <= x <= y < 100
  {
    var y' := y - x;
    /*
      -x <= 0 <= y - x < 100 - x
      0 <= y' < 100 - x
    */

    assert 0 <= y' < 100 - x;
  }

  method C(x: int, y: int)
    requires x % 2 == 0 && y < 100
  {
    var x' := y;
    var y' := x;

    assert x' < 100;
    assert y' % 2 == 0;
  }
}

module Exercise_2_7 {
// Come up with predicate, as general as possible, st. the Hoare triple holds
  method A(x: int)
  {
    var x := 400;

    assert x == 400;
  }

  method B(x: int)
    requires x % 2 == 1;
  {
    var x := x + 3;

    assert x % 2 == 0;
  }

  method C(x: int, y: int)
    requires y <= 65
  {
    var x := 65;
    
    assert y <= x;
  } 
}

module Exercise_2_8 {
// Come up with predicate, as general as possible, st. the Hoare triple holds
  method A(x: int, y: int)
    requires x < y
  {
    var b := y < 10;

    assert b ==> (x < y);
  }

  method B(x: int, y: int)
    requires 0 <= x <= 50
    requires y < 0
  {
    var x, y := 2*x, x + y;

    assert 0 <= x <= 100 && y <= x;
  }
}

module Test_Old {
  method Test(x: int)
    requires x == 5
  {
    var x := 10;

    assert old(x) == 5;
  }
}

module Exercise_2_9 {
// verify the following program correctly swaps
  method Swap(x: bv32, y: bv32)
  {
      assert (x ^ y) ^ y == x;
    var x' := x ^ y;
      assert x' ^ y == x;
      assert 0 ^ y == y && x' ^ y == x;
      assert x' ^ (x' ^ y) == y && (x' ^ y) == x;
    var y' := x' ^ y;
      assert x' ^ y' == y && y' == x;
    x' := x' ^ y';
      assert x' == y && y' == x;
  }
}

// ! not sure why
module Exercise_2_10 {
// Find the error in the following proof
  method Error(x: int, y: int)
    requires x == 0 && y == 6
  {
    var x' := x;
    var y' := y;

    x' := x' + 2;
      assert x' == 2 && y' == 6;
      assert x' + y' == 8;
    y' := x' + y';
    assert y' == 8;
  }
}

module Exercise_2_11 {
// Fill in the weakest preconditions
  method A(x: int, y: int, z: int)
    requires z > 7
  {
      assert 6 < 10 && 7 < z;
    var x', y' := 6,7;

    assert x' < 10 && y' < z;
  }

  method B(x: int, y: int)
    requires x == 4
  {
      assert x - 1 == 3;
      assert (2 * x) - (x + 1) == 3;
    var x', y' := x + 1, 2 * x;

    assert y' - x' == 3;
  }

  method C(x: int, y: int)
    requires x == 2;
  {
    var x', y' := x, y;
      assert (x' + 1) == 3;
    x' := x' + 1;
      assert x' == 3;
      assert (2 * x') - x' == 3;
    y' := 2 * x';

    assert y' - x' == 3;
  }
}

module Exercise_2_12 {
  // Prove: {{ true }} var x; x := x * x {{ 0 <= x }}
  method A(x: int) {
    var x';
    assert 0 <= x * x;
    x' := x * x;
    assert 0 <= x';
  }
}

module Exercise_2_13 {
  // Calculate the strongest postcondition, simplifying when possible

  method A(x: int, y: int)
    requires y == 10
  {
    var x' := 12;
    // exists x_0: int :: y == 10 && x' == 12;
    assert y == 10 && x' == 12;
  }

  method B(x: int, y: int)
    requires 98 <= y
  {
    var x' := x + 1;
    // exists x_0: int :: 98 <= y && x' == x_0 + 1;
    assert 98 <= y && x' == x + 1;
  }

  method C(x: int, y: int)
    requires 98 <= x
  {
    var x' := x + 1;
    // exists x_0: int :: 98 <= x_0 && x' == x_0 + 1
    assert 98 <= x && x' == x + 1;
  }

  method D(x: int, y: int)
    requires 98 <= y < x
  {
    var x' := 3 * y + x;
    // exists x_0: int :: 98 <= y < x_0 && x' == 3 * y + x_0
    assert 98 <= y < x && x' == 3 * y + x;
  }
}

module Exercise_2_14 {
  // verify correctness of swap programs using strongest post conditions
  method Swap1(x: int, y: int) returns (x': int, y': int)
    ensures x' == y && y' == x
  {
    var tmp := x;
    assert tmp == x;
    x' := y;
    assert x' == y && tmp == x;
    y' := tmp;
    assert x' == y && tmp == x && y' == tmp;
    assert x' == y && y' == x;
  }
}

module Exercise_2_15 {
  // Compute the weakest precondition of the programs with respect to the postcondition:
  // x + y <= 100
  method A(x: int, y: int) returns (x': int, y': int)
    requires 20 + y <= 100
  {
    assert 20 + y <= 100;
    x' := x;
    y' := y;

    assert 20 + y' <= 100;
    x' := 20;
    
    assert x' + y' <= 100;
  }

  method B(x: int, y: int) returns (x': int, y': int)
    requires x + y <= 99
  {
    x' := x;
    y' := y;

    assert x' + y' <= 99;
    assert x' + 1 + y' <= 100;
    x' := x' + 1;

    assert x' + y' <= 100;
  }

  method C(x: int, y: int) returns (x': int, y': int)
    requires 2 * x + y <= 100
  {
    x' := x;
    y' := y;

    assert 2 * x' + y' <= 100;
    x' := 2 * x';

    assert x' + y' <= 100;
  }

  method D(x: int, y: int) returns (x': int, y': int)
    requires -x + y <= 100
  {
    x' := x;
    y' := y;

    assert -x' + y' <= 100;
    x' := -x';

    assert x' + y' <= 100;
  }

  method E(x: int, y: int) returns (x': int, y': int)
    requires y <= 50
  {
    x' := x;
    y' := y;

    assert y' <= 50;
    assert y' + y' <= 100;
    x' := y';

    assert x' + y' <= 100;
  }

  method F(x: int, y: int) returns (x': int, y': int)
    requires x + 2 * y <= 100
  {
    x' := x;
    y' := y;

    assert x' + y' + y' <= 100;
    x' := x' + y';

    assert x' + y' <= 100;
  }

  method G(x: int, y: int) returns (x': int, y': int)
    requires -x + 2 * y <= 100
  {
    x' := x;
    y' := y;

    assert y' - x' + y' <= 100;
    x' := y' - x';

    assert x' + y' <= 100;
  }

  method H(x: int, y: int) returns (x': int, y': int)
    requires x + 2 * y <= 100
  {
    x' := x;
    y' := y;

    assert x' + y' + y' <= 100;
    x' := x' + y';

    assert x' + y' <= 100;
  }

  method I(x: int, y: int) returns (x': int, y': int)
    requires x + y <= 100
  {
    x' := x;
    y' := y;

    // for all z :: x' + y' <= 100
    var z;

    assert x' + y' <= 100;
    z := x' + y';

    assert x' + y' <= 100;
  }
}

module Exercise_2_16 {
  method A(x: int, y: int) returns (x': int, y': int)
    requires x + y <= 100
  {
    x' := x;
    y' := y;

    x' := 5;

    // Make the witness explicit in the predicate.
    // assert x' == 5;
    // var x_0 := 100 - y';
    // assert x_0 + y' <= 100;
    // assert exists w: int {:trigger w + y'} :: w == x_0 && w + y' <= 100;

    // assert exists x_0: int :: x_0 + y' <= 100
    assert x + y' <= 100 && x' == 5;
  }

  method B(x: int, y: int) returns (x': int, y': int)
    requires x + y <= 100
  {
    x' := x;
    y' := y;

    x' := x + 1;
    // assert exists x_0: int :: x_0 + y' <= 100 && x' == x_0 + 1
    assert x + y' <= 100 && x' == x + 1;
  }

  method C(x: int, y: int) returns (x': int, y': int)
    requires x + y <= 100
  {
    x' := x;
    y' := y;

    x' := 2 * y;
    // assert exists x_0: int :: x_0 + y' <= 100 && x' == 2 * y
    assert x + y' <= 100 && x' == 2 * y;
  }

  method D(x: int, y: int) returns (x': int, y': int)
    requires x + y <= 100
  {
    x' := x;
    y' := y;

    var z := x' + y';
    //assert exists z_0: int :: x' + y' <= 100 && z == x' + y'
    assert x' + y' <= 100 && z == x' + y';
  }

}

method Main() {
  print "Hello, Dafny!";
}