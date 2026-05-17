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

module Exercise_2_17 {
  method A()
    // requires forall x: int :: x <= 100
    requires false;
  {
    var x : int;
    assert x <= 100;
  }

  method B()
  {
    var x : int;
    // assert x <= 100;
    assert false;
  }
}

module Exercise_2_18 {
  method A(x': int, y': int)
    // Draw a decorated flow diagram for the conditional statement
    // if x < 3 { x, y := x + 1, 10; } else { y := x};
  {
    var x, y : int := x', y';

    if x < 3 {
      assert x < 3;

      x, y := x + 1, 10;
      //exists x_0 :: x_0 < 3 && x == x_0 + 1
      assert y == 10;
    }
    else {
      assert x >= 3;

      y := x;
      // exists y_0 :: x >= 3 && y == x
      assert x >= 3 && y == x;
    }
    // (exists x_0 :: x_0 < 3 && x == x_0 + 1 && y == 10) || (y == x && x >= 3)
    assert (y == 10) || (y == x && x >= 3);
  }
  // WP is trivial, as there is no postcondition

  method B_forward(x': int, y': int)
    requires x' + y' == 100
  {
    var x, y : int := x', y';

    if x < 3 {
      assert x + y == 100 && x < 3;

      x, y := x + 1, 10;
      //exists x_0, y_0 :: x_0 + y_0 == 100 && x_0 < 3 && x == x_0 + 1 && y == 10
      //exists x - 1 + y_0 == 100 && x - 1 < 3 && y_0 == 10
      assert x < 4 && y == 10;
    }
    else {
      assert x + y == 100 && x >= 3;

      y := x;
      //exists y_0 :: x + y_0 == 100 && x >= 3 && y == x
      assert x >= 3 && y == x;
    }
    //exists y_0 :: (x + y_0 == 101 && x < 4 && y == 10)
    // || (x + y_0 == 100 && x >= 3 && y == x)
    assert (x < 4 && y == 10) || (x >= 3 && y == x);
  }

  method B_backward(x': int, y': int)
    requires x' == 50
  {
    var x, y : int := x', y';

    assert x >= 3 && (x >= 3 ==> x == 50);
    if x < 3{

      assert x == 89;
      assert x + 1 + 10 == 100;
      x, y := x + 1, 10;
    }
    else {

      assert x == 50;
      assert x + x == 100;
      y := x;
    }

    assert x + y == 100;
  }
}

module Exercise_2_19 {
  method A(x': int)
    requires x' < 100
  {
    var x := x';
    var y;

    if x < 20 {
      y := 3;

      //SP [[ y := 3, x < 20 && x < 100 ]] == x < 20 && y == 3
      assert x < 20 && y == 3;
    }
    else {
      y := 2;

      //SP [[ y := 2, x >= 20 && x < 100 ]]
      assert x >= 20 && x < 100 && y == 2;
    }

    assert (x < 20 && y == 3) || (x >= 20 && x < 100 && y == 2);
  }
}

module Exercise_2_20 {
  method A(x': int, y' : int)
    requires x' == 20 || x' == 19
  {
    var x := x';
    var y := y';

    // assert x == 20 || x == 19;
    assert (x >= 20 ==> x == 20) && (x < 20 ==> x == 19);

    // x >= 20 || x == 19;
    // x < 20 == > x == 19;
    if x < 20 {
      assert x == 19;
      assert x + 3 == 22;
      // WP [[ y := 3, x + y == 22]]
      y := 3;
    }
    // x < 20 || x == 20
    // x >= 20 == > x == 20
    else {
      assert x == 20;
      assert x + 2 == 22;
      // WP [[ y := 2, x + y == 22]]
      y := 2;
    }
    assert x + y == 22;
  }
}

module Exercise_2_21 {
  method A(x': int)
    requires x' != 5
  {
    var x := x';
    var y;

    assert x < 8 ==> x != 5;
    assert (x < 8 ==> x != 5) && (x >= 8 ==> true);
    // B ==> x != 5 && !B ==> true
    // B ==> WP [[ S, y < 10]] && !B ==> WP [[ T, y < 10]]
    if x < 8 {
      assert x != 5;
      // !B
      // B ==> false && !B ==> true
      // B ==> WP [[ s, y < 10]] && !B == > WP [[ t, y < 10]]
      // WP [[ S, y < 10 ]]
      if x == 5 {
        assert false;
        // WP [[ y := 10, y < 10]]
        y := 10;
      } else {
        assert true;
        // WP [[ y := 2, y < 10]]
        y := 2;
      }
    } else{
      assert true;
      // WP [[ y := 0, y < 10]]
      y := 0;
    }

    assert y < 10;
  }
}

module Exercise_2_22 {
  method A(x': int)
    requires x' >= 10
  {
    var x := x';
    var y;

    // x >= 10
    // (x < 10 ==> x >= 20) && (x >= 10 ==> true)
    if x < 10 {
      assert x >= 20;
      // x < 20 ==> false && x >= 20 ==> true;
      // WP [[ S, y % 2 == 0]]
      if x < 20 {
        assert false;
        y := 1;
      } else {
        assert true;
        y := 2;
      }
    } else {
      assert true;
      y := 4;
    }

    assert y % 2 == 0;
  }
}

module Exercise_2_23 {
  method A(x': int, y': int)
    requires (x' >= 4 && x' < 8)
    || (x' >= 32 && y' % 2 == 0)
    || (y' % 2 == 0 && x' < 8)
  {
    var x := x';
    var y := y';


    assert (x >= 4 && x < 8)
    || (x >= 32 && y % 2 == 0)
    || (y % 2 == 0 && x < 8);

    // (x >= 4 && x < 8)
    // || (x >= 4 && x >= 32 && y % 2 == 0) == (x >= 32 && y % 2 == 0)
    // || (y % 2 == 0 && x < 8)
    // || (y % 2 == 0 && x >= 32)
    assert (x >= 4 || y % 2 == 0) && (x < 8 || (x >= 32 && y % 2 == 0));
    assert (x >= 8 || x >= 4 || y % 2 == 0) && (x < 8 || (x >= 32 && y % 2 == 0));
    assert ( x < 8 ==> (x >= 4 || y % 2 == 0)) && (x >= 8 ==> (x >= 32 && y % 2 == 0));
    if x < 8 {
      // x >= 4 || y % 2 == 0
      // x < 4 ==> y % 2 == 0
      // (x < 4 ==> y % 2 == 0) && (x >= 4 ==> true)
      if x < 4 {
        assert y % 2 == 0;
        x := x + 1;
      } else {
        assert true;
        y := 2;
      }
    } else {
      // x >= 32 && y % 2 == 0
      // x >= 32 && (x >= 32 ==> y % 2 == 0)
      // (x < 32 ==> false) && (x >= 32 ==> y % 2 == 0)
      if x < 32 {
        assert false;
        y := 1;
      } else {
        assert y % 2 == 0;
        // nothing
      }
    }

    assert y % 2 == 0;
  }
}

module Exercise_2_24 {
  method A(x': int, y': int)
    requires x' == 2 || (x' >= 34 && x' < 55)
  {
    var x := x';
    var y := y';

    if x < 34 {

      assert x == 2;
      if x == 2 {

        assert true;
        y := x + 1;
      } else {

        assert false;
        y := 233;
      }

      assert 0 <= y < 100;
    } else {

      assert x < 55;
      assert (x < 55 ==> true) && (x >= 55 ==> false);
      if x < 55 {

        assert true;
        y := 21;
      } else {

        assert false;
        y := 144;
      }

      assert 0 <= y < 100;
    }

    assert 0 <= y < 100;
  }
}

module Exercise_2_25 {
  // a) {{ 0 <= x }} x := x + 1 {{ -2 <= x }} y := 0 {{ -10 <= x }}
    // valid
  // b) {{ 0 <= x }} x := x + 1 {{ true }} x := x + 1 {{ 2 <= x }}
    // the first is valid trivially. the second is now invalid, as x could be anything.
  // c) {{ 0 <= x }} x := x + 1; x := x + 1 {{ 2 <= x }}
    // the smallest x can be is 0, afterwards its 2, so valid
  // d) {{ 0 <= x }} x := 3 * x; x := x + 1 {{ 3 <= x }}
    // invalid. if x starts as 0, x ends up as 1, which is not >= 3
  // e) {{ x < 2 }} y := x + 5; x := 2 * x {{ x < y }}
    // this one is tuff.
    // y = x_0 + 5
    // x = 2 * x_0
    // x_0 < 2
    // x_0 + x_0 < 2 + x_0
    // x < 2 + x_0
    // x < 2 + x_0 < x_0 + 5 == y
    // valid
}

module Exercise_2_26 {
  //find WP of x + y <= 100, working backwards
  method A(x': int, y': int) returns (x: int, y: int)
    requires 2 * x' + y' <= 98
  {
    x := x';
    y := y';

    assert x + 1 + x + 1 + y <= 100;
    x := x + 1;

    assert x + x + y <= 100;
    y := x + y;

    assert x + y <= 100;
  }

  method B(x': int, y': int) returns (x: int, y: int)
    requires 2 * x' + y' <= 99
  {
    x := x';
    y := y';

    assert x + x + y <= 99;
    y := x + y;

    assert x + y <= 99;
    assert x + 1 + y <= 100;
    x := x + 1;

    assert x + y <= 100;
  }

  method C(x': int, y': int) returns (x: int, y: int)
    requires 2 * x' + y' <= 99
  {
    x := x';
    y := y';

    assert x + 1 + x + y <= 100;
    x, y := x + 1, x + y;

    assert x + y <= 100;
  }
}

module Exercise_2_27 {
  // SP with respect to x + y <= 100
  method A(x': int, y': int) returns (x: int, y: int)
    requires x' + y' <= 100
  {
    x := x';
    y := y';

    x := x + 1;
    //exists x_0 :: x_0 + y <= 100 && x == x_0 + 1
    // x_0 == x - 1
    // x - 1 + y <= 100
    assert x - 1 + y <= 100;
    assert x + y <= 101;

    y := x + y;
    //exists y_0 :: x + y_0 <= 101 && y == x + y_0
    // y_0 :: x + y_0 <= 101 && y_0 == y - x
    assert x + y - x <= 101;
    assert y <= 101;
  }

  method B(x': int, y': int) returns (x: int, y: int)
    requires x' + y' <= 100
  {
    x := x';
    y := y';

    y := x + y;
    //exists y_0 :: x + y_0 <= 100 && y == x + y_0
    // exists y_0 :: x + y_0 <= 100 && y_0 == y - x
    // x + y - x <= 100
    assert y <= 100;

    x := x + 1;
    //exists x_0 :: y <= 100 && x == x_0 + 1
    assert y <= 100;
  }

  method C(x': int, y': int) returns (x: int, y: int)
    requires x' + y' <= 100
  {
    x := x';
    y := y';

    x, y := x + 1, x + y;
    // exists x_0, y_0 :: x_0 + y_0 <= 100 && x == x_0 + 1 && y == x_0 + y_0
    // exists x_0, y_0 :: y <= 100 && x == x_0 + 1
    assert y <= 100;
  }
}

module Exercise_2_28 {
  // SP and WP for x + y < 100
  method A_SP(x': int, y': int) returns (x: int, y: int)
    requires x' + y' < 100
  {
    x := x';
    y := y';

    x := 32;
    //exists x_0 :: x_0 + y < 100 && x == 32
    assert x == 32;

    y := 40;
    assert x == 32 && y == 40;
  }

  method A_WP(x': int, y': int) returns (x: int, y: int)
  {
    x := x';
    y := y';

    assert 32 < 60;
    x := 32;

    assert x < 60;
    assert x + 40 < 100;    
    y := 40;

    assert x + y < 100;
  }

  method B_SP(x': int, y': int) returns (x: int, y: int)
    requires x' + y' < 100
  {
    x := x';
    y := y';

    x := x + 2;
    //exists x_0 :: x_0 + y < 100 && x == x_0 + 2
    //x_0 = x - 2
    // x - 2 + y < 100
    assert x + y < 102;
    
    y := y - 3*x;
    //exists y_0 :: x + y_0 < 102 && y == y_0 - 3*x
    // y_0 == y + 3*x
    // x + y + 3*x < 102
    assert 4*x + y < 102;
  }

  method B_WP(x': int, y': int) returns (x: int, y: int)
    requires -2*x' + y' < 104
  {
    x := x';
    y := y';

    assert -2*x + y < 104;
    assert -2 * x - 4 + y < 100;
    assert -2 * (x + 2) + y < 100;
    x := x + 2;

    assert -2*x + y < 100;
    assert x + y - 3*x < 100;
    y := y - 3*x;

    assert x + y < 100;
  }
}

module Exercise_2_29 {
  //WP
  method A(x': int, y': int) returns (x: int, y: int)
  {
    x := x';
    y := y';

    // for all X, true
    var X;

    assert 10 <= 100;
    X := 10;

    assert X <= 100;
  }

  //SP
  method B(x': int, y': int) returns (x: int, y: int)
    requires x' <= 100
  {
    x := x';
    y := y';

    var X;
    //exists X :: x < 100;

    X := 10;
    assert X == 10;
  }
}

module Exercise_2_30 {
  // SP
  method A(x': int, y': int) returns (x: int, y: int)
    requires x' < 10
  {
    x := x';
    y := y';

    if x % 2 == 0 {
      assert x < 10 && x % 2 == 0;
      y := y + 3;
      //exists y_0 :: blah blah && y == y_0 + 3
      assert x < 10 && x % 2 == 0;
    }
    else {
      assert x < 10 && x % 2 == 1;
      y := 4;
      assert x < 10 && x % 2 == 1 && y == 4;
    }
    assert (x < 10 && x % 2 == 0) || (x < 10 && x % 2 == 1 && y == 4);
    assert x < 10 && ((x % 2 == 0) || (x % 2 == 1 && y == 4));

    if y < 10 {
      assert x < 10 && ((x % 2 == 0) || (x % 2 == 1 && y == 4)) && y < 10;
      y := x + y;
      // exists y_0 :: x < 10 && ((x % 2 == 0) || (x % 2 == 1 && y_0 == 4)) && y_0 < 10 && y == x + y_0
      // y_0 == y - x
      assert x < 10 && ((x % 2 == 0) || (x % 2 == 1 && y - x == 4)) && y - x < 10;
    }
    else {
      assert x < 10 && ((x % 2 == 0) || (x % 2 == 1 && y == 4)) && y >= 10;
      assert x < 10 && x % 2 == 0 && y >= 10;
      x := 8;
      //exists x_0 :: x_0 < 10 && x_0 % 2 == 0 && y >= 10 && x == 8
      assert x == 8 && y >= 10;
    }

    assert (x < 10 && ((x % 2 == 0) || (x % 2 == 1 && y - x == 4)) && y - x < 10) || (x == 8 && y >= 10);
  }

  // WP
  method B(x': int, y': int) returns (x: int, y: int)
    requires x' < 10 || (x' % 2 == 0 && y' >= 7)
  {
    x := x';
    y := y';

    assert x < 10 || (x % 2 == 0 && y >= 7);
    assert x < 10 || ((x % 2 == 1 || y >= 7) && x % 2 ==0);
    assert (x%2 == 1 || y >= 7 || x < 10 ) && (x % 2 == 0 || x < 10);
    assert (x%2 == 1 || (y >= 7 || x < 10)) && (x % 2 == 0 || x < 10);
    assert x % 2 == 0 ==> (y >= 7 || x < 10) && (x % 2 == 1 ==> x < 10);
    if x % 2 == 0 {
      assert y >= 7 || x < 10;
      assert y + 3 >= 10 || x < 10;
      y := y + 3;
    }
    else{
      assert x < 10;
      assert 4 >= 10 || x < 10;
      y := 4;
    }

    assert y >= 10 || x < 10;
    assert (y >= 10 || x < 10) && (y < 10 || true);
    // y < 10 ==> x < 10 && y >= 10 ==> true
    if y < 10 {
      assert x < 10;
      y := x + y;
    }
    else {
      assert true;
      x := 8;
    }

    assert x < 10;
  }
}

module Exercise_2_31 {
  method {:axiom} Abs(x: int) returns (y: int)
    ensures 0 <= y && (x == y || x == -y)
  
  method A(u : int)
    requires u != 0
  {

    // -7*u >= 0 && u < -7*u === u <= 0 && 6*u < 0 === u < 0
    // ||
    // 7*u >= 0 && u < 7*u === u >= 0 && 0 < 6*u === 0 < u

    // forall y' :: 0 <= y' && (7 * u == y' || 7 * u == -y) ==> u < y'
    // forall y' :: (0 <= y && (x == y || x == -y))[x,y := 7 * u, y'] ==> (u < t)[t := y']
    var t := Abs(7 * u);

    assert u < t;
  }
}

module Exercise_2_32 {
  method {:axiom} Max(x: int, y: int) returns (m: int)
    ensures m == x || m == y
    ensures x <= m && y <= m
  
  method A(u: int)
    requires u > 7 || u % 2 == 1
  {
    // u >= 7 || u % 2 == 1
    // u <= 7 ==> u % 2 == 1
    // 2 * u <= u + 7 ==> (u + 7) % 2 == 0
    // {one point rule}
    // forall m' :: (m' == u + 7 && 2 * u <= u + 7 ==> (u + 7) % 2 == 0)
    // {simplify}
    // forall m' :: (m' == 2 * u && u + 7 <= 2 * u ==> 2*u % 2 == 0) && (m' == u + 7 && 2 * u <= u + 7 ==> (u + 7) % 2 == 0)
    // {(A || B) ==> C == > (A ==> C) && (B ==> C)}
    // forall m' :: (m' == 2 * u && u + 7 <= 2*u || m' == u + 7 && 2 * u <= u + 7) ==> m' % 2 == 0
    // {simplify}
    // forall m' :: (m' == 2 * u && 2 * u <= m' && u + 7 <= m' || m' == u + 7 && 2 * u <= m' && u + 7 <= m') ==> m' % 2 == 0
    // {distribute}
    // forall m' :: (m' == 2 * u || m' == u + 7) && (2 * u <= m' && u + 7 <= m') ==> m' % 2 == 0
    var t := Max(2 * u, u + 7);

    assert t % 2 == 0;
  }
}

method Main() {
  print "Hello, Dafny!";
}