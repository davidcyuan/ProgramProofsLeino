// Triple
  method Triple (x: int) returns (r: int)
    ensures r == 3 * x
    {
      var y := 2 * x;
      r := x + y;
    }
  method Triple2 (x: int) returns (r: int){
    if x == 0 {
      r := 0;
    }
    else {
      var y := 2 * x;
      r := x + y;
    }
    assert r == 3 * x;
  }
  method Triple3 (x: int) returns (r: int) {
    if {
      case x < 18 =>
        var a, b := 2 * x, 4 * x;
        r := (a + b ) / 2;
      case 0 <= x =>
        var y := 2 * x;
        r := x + y;
    }
    assert r == 3 * x;
  }
  method Triple4 (x: int) returns (r: int)
    requires x == 0
    ensures r == 3 * x
    {
      var y := x / 2;
      r := 6 * y;
    }

  method Caller () {
    var t := Triple(18);
    assert t < 100;
  }

// Max Sum
  method Min (x: int, y: int) returns (m: int)
    ensures m <= x && m <= y
    ensures m == x || m == y
    {
      if x < y {
        m := x;
      } else if y < x {
        m := y;
      }
      else{
        m := x;
      }
    }

  method MaxSum(x: int, y: int) returns (s: int, m: int)
    ensures m >= x && m >= y && (m == x || m == y)
    ensures s == x + y
    {
      if x >= y {
        m := x;
      } else {
        m := y;
      }
      s := x + y;
    }

  method MSCaller(){
    var sum, max := MaxSum(1928, 1);
    assert sum == 1929;
    assert max == 1928;
  }
  method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
    requires s <= 2 * m
    ensures s == x + y
    ensures (m == x || m == y) && m >= x && m >= y
    {
      x := m;
      y := s - x;
    }
  method TestMaxSum(x: int, y: int){
    var s, m := MaxSum(x, y);
    var x_, y_ := ReconstructFromMaxSum(s, m);
    assert (x_ == x && y_ == y) || (x_ == y && y_ == x);
  }

// Average
  function Average(a: int, b: int): int{
    (a + b) / 2 
  }
  method Triple'(x: int) returns (r: int)
    ensures Average(r, 3 * x) == 3 * x
    ensures Average(r + 1, 3 * x) == 3 * x
    // {
    //   //r equals someting that averages to 3*x with 3*x, but is not 3 * x
    //   //r := 3 * x + 1;
    //   r := 3 * x + 1;
    // }
  method CheckTriple'(x: int){
    var r1 := Triple(x);
    var r2 := Triple'(x);
    assert r1 == r2;
  }

  function Average''(a: int, b: int): int{
    (a + b) / 2 
  }
  ghost method Triple''(x: int) returns (r: int)
    ensures r == 3 * x
    {
      ghost var bunny := 100;
      r := Average''(2 * x, 4 * x);
    }

// 1.11
function F(): int{
  29
}

method M() returns (r: int){
  r := 29;
}

method Caller'() {
  var a := F();
  var b := M();
  assert a == 29;
  assert b == 29;
}


method Main()
{
  // var t := Triple(18);      // sets t to 54
  // print t;
}