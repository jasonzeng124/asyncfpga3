module {
  handshake.func @straight(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["a", "b", "start"], resNames = ["out0", "end"]} {
    %0:4 = fork [4] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <i32>
    %1:4 = fork [4] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %3 = constant %2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 7 : i32} : <>, <i32>
    %4 = source {handshake.bb = 0 : ui32, handshake.name = "source1"} : <>
    %5 = constant %4 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 3 : i32} : <>, <i32>
    %6 = source {handshake.bb = 0 : ui32, handshake.name = "source2"} : <>
    %7 = constant %6 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = 2 : i32} : <>, <i32>
    %8 = source {handshake.bb = 0 : ui32, handshake.name = "source3"} : <>
    %9 = constant %8 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = 11 : i32} : <>, <i32>
    %10 = source {handshake.bb = 0 : ui32, handshake.name = "source4"} : <>
    %11 = constant %10 {handshake.bb = 0 : ui32, handshake.name = "constant4", value = -1640531527 : i32} : <>, <i32>
    %12 = addi %1#3, %0#3 {handshake.bb = 0 : ui32, handshake.name = "addi0"} : <i32>
    %13:2 = fork [2] %12 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i32>
    %14 = subi %1#2, %0#2 {handshake.bb = 0 : ui32, handshake.name = "subi0"} : <i32>
    %15:2 = fork [2] %14 {handshake.bb = 0 : ui32, handshake.name = "fork3"} : <i32>
    %16 = shli %15#1, %3 {handshake.bb = 0 : ui32, handshake.name = "shli0"} : <i32>
    %17 = xori %13#1, %16 {handshake.bb = 0 : ui32, handshake.name = "xori0"} : <i32>
    %18 = shrui %1#1, %5 {handshake.bb = 0 : ui32, handshake.name = "shrui0"} : <i32>
    %19 = addi %17, %18 {handshake.bb = 0 : ui32, handshake.name = "addi1"} : <i32>
    %20 = shli %0#1, %7 {handshake.bb = 0 : ui32, handshake.name = "shli1"} : <i32>
    %21 = subi %19, %20 {handshake.bb = 0 : ui32, handshake.name = "subi1"} : <i32>
    %22:2 = fork [2] %21 {handshake.bb = 0 : ui32, handshake.name = "fork4"} : <i32>
    %23 = shrui %22#1, %9 {handshake.bb = 0 : ui32, handshake.name = "shrui1"} : <i32>
    %24 = xori %22#0, %23 {handshake.bb = 0 : ui32, handshake.name = "xori1"} : <i32>
    %25 = addi %24, %11 {handshake.bb = 0 : ui32, handshake.name = "addi2"} : <i32>
    %26 = andi %13#0, %15#0 {handshake.bb = 0 : ui32, handshake.name = "andi0"} : <i32>
    %27 = subi %25, %26 {handshake.bb = 0 : ui32, handshake.name = "subi2"} : <i32>
    %28 = ori %1#0, %0#0 {handshake.bb = 0 : ui32, handshake.name = "ori0"} : <i32>
    %29 = addi %27, %28 {handshake.bb = 0 : ui32, handshake.name = "addi3"} : <i32>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %29, %arg2 : <i32>, <>
  }
}

