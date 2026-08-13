module {
  handshake.func @backtrackToArgument(%arg0: !handshake.control<>, ...) attributes {argNames = ["start"], resNames = []} {
    %0 = fork [1] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1 = fork [1] %0 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <>
    %2 = fork [1] %1 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <>
    end {handshake.name = "end0"}
  }
}


// -----
module {
  handshake.func @backtrackToKnownBB(%arg0: !handshake.control<>, ...) attributes {argNames = ["start"], resNames = []} {
    %0 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br0"} : <>
    %1 = merge %0 {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <>
    %2:2 = fork [2] %1 {handshake.bb = 1 : ui32, handshake.name = "fork0"} : <>
    %3 = fork [1] %2#0 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <>
    %4 = fork [1] %2#1 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    end {handshake.name = "end0"}
  }
}


// -----
module {
  handshake.func @backtrackConflict(%arg0: !handshake.control<>, ...) attributes {argNames = ["start"], resNames = []} {
    %0 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br0"} : <>
    %1 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <>
    %2 = merge %0 {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <>
    %3 = merge %1 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <>
    %4 = merge %2, %3 {handshake.name = "merge2"} : <>
    end {handshake.name = "end0"}
  }
}


// -----
module {
  handshake.func @forwardToKnownBB(%arg0: !handshake.control<>, ...) attributes {argNames = ["start"], resNames = []} {
    %0:2 = fork [2] %arg0 {handshake.bb = 1 : ui32, handshake.name = "fork0"} : <>
    %1 = merge %0#0 {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <>
    %2 = merge %0#1 {handshake.bb = 1 : ui32, handshake.name = "merge1"} : <>
    end {handshake.name = "end0"}
  }
}


// -----
module {
  handshake.func @forwardConflict(%arg0: !handshake.control<>, ...) attributes {argNames = ["start"], resNames = []} {
    %0 = merge %arg0 {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <>
    %1 = merge %arg0 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <>
    %2 = merge %0, %1 {handshake.name = "merge2"} : <>
    %3:2 = fork [2] %2 {handshake.name = "fork0"} : <>
    %4 = merge %3#0 {handshake.bb = 1 : ui32, handshake.name = "merge3"} : <>
    %5 = merge %3#1 {handshake.bb = 2 : ui32, handshake.name = "merge4"} : <>
    end {handshake.name = "end0"}
  }
}


// -----
module {
  handshake.func @forwardOverBackward(%arg0: !handshake.control<>, ...) attributes {argNames = ["start"], resNames = []} {
    %0 = br %arg0 {handshake.bb = 1 : ui32, handshake.name = "br0"} : <>
    %1:2 = fork [2] %0 {handshake.bb = 2 : ui32, handshake.name = "fork0"} : <>
    %2 = merge %1#0 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <>
    %3 = merge %1#1 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <>
    end {handshake.name = "end0"}
  }
}


// -----
module {
  handshake.func @backwardOverForward(%arg0: !handshake.control<>, ...) attributes {argNames = ["start"], resNames = []} {
    %0 = br %arg0 {handshake.bb = 1 : ui32, handshake.name = "br0"} : <>
    %1:2 = fork [2] %0 {handshake.bb = 1 : ui32, handshake.name = "fork0"} : <>
    %2 = merge %1#0 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <>
    %3 = merge %1#1 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <>
    end {handshake.name = "end0"}
  }
}

