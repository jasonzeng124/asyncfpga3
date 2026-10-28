module {
  handshake.func @constantFoldExtUI(%arg0: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["start"], resNames = ["out0"]} {
    %0 = constant %arg0 {value = 64170 : i32} : <>, <i32>
    end %0 : <i32>
  }
}


// -----
module {
  handshake.func @constantFoldExtSI(%arg0: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["start"], resNames = ["out0"]} {
    %0 = constant %arg0 {value = -1366 : i32} : <>, <i32>
    end %0 : <i32>
  }
}


// -----
module {
  handshake.func @constantFoldTruncI(%arg0: !handshake.control<>, ...) -> !handshake.channel<i8> attributes {argNames = ["start"], resNames = ["out0"]} {
    %0 = constant %arg0 {value = -86 : i8} : <>, <i8>
    end %0 : <i8>
  }
}

