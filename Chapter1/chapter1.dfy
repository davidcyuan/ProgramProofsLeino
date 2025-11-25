// change

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

method Main()
{
  // var t := Triple(18);      // sets t to 54
  // print t;
}