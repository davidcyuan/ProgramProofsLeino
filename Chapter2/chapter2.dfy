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
     

method Main() {
  print "Hello, Dafny!";
}