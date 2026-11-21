module {
  memref.global "private" constant @".str" : memref<4xi8> = dense<[91, 50, 93, 0]> {alignment = 1 : i64, handshake.name = "global0"}
  memref.global "private" constant @".str.1" : memref<6xi8> = dense<[115, 116, 97, 114, 116, 0]> {alignment = 1 : i64, handshake.name = "global1"}
  memref.global "private" constant @".str.2" : memref<4xi8> = dense<[105, 110, 116, 0]> {alignment = 1 : i64, handshake.name = "global2"}
  memref.global "private" constant @".str.3" : memref<1xi8> = dense<0> {alignment = 1 : i64, handshake.name = "global3"}
  memref.global "private" constant @".str.4" : memref<4xi8> = dense<[101, 110, 100, 0]> {alignment = 1 : i64, handshake.name = "global4"}
  func.func @nested_conditionals_1(%arg0: memref<100xi32> {handshake.arg_name = "a"}, %arg1: i32 {handshake.arg_name = "c"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb4
    %c8_i32 = arith.constant {handshake.name = "constant8"} 8 : i32
    %c2_i32 = arith.constant {handshake.name = "constant9"} 2 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg0[%2] {dynamatic.predict = {location = "start", marker = 0 : i32, type = "int", values = "[2]"}, dynamatic.predict.result_idx = 0 : i32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<100xi32>
    %4 = arith.addi %3, %c2_i32 {handshake.name = "addi0"} : i32
    %5 = arith.cmpi sgt, %3, %c8_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %5, ^bb2, ^bb3 {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb1
    %c1_i32 = arith.constant {handshake.name = "constant10"} 1 : i32
    %c5_i32 = arith.constant {handshake.name = "constant11"} 5 : i32
    %6 = arith.cmpi sgt, %arg1, %c5_i32 {handshake.name = "cmpi1"} : i32
    %7 = arith.shli %4, %c1_i32 {handshake.name = "shli0"} : i32
    %8 = arith.addi %4, %arg1 {handshake.name = "addi1"} : i32
    %9 = arith.select %6, %7, %8 {handshake.name = "select0"} : i32
    cf.br ^bb4(%9 : i32) {handshake.name = "br1"}
  ^bb3:  // pred: ^bb1
    %c-1_i32 = arith.constant {handshake.name = "constant12"} -1 : i32
    %c0_i32_0 = arith.constant {handshake.name = "constant13"} 0 : i32
    %10 = arith.cmpi eq, %arg1, %c0_i32_0 {handshake.name = "cmpi2"} : i32
    %11 = arith.addi %3, %c-1_i32 {handshake.name = "addi2"} : i32
    %12 = arith.muli %4, %arg1 {handshake.name = "muli0"} : i32
    %13 = arith.select %10, %11, %12 {handshake.name = "select1"} : i32
    cf.br ^bb4(%13 : i32) {handshake.name = "br2"}
  ^bb4(%14: i32):  // 2 preds: ^bb2, ^bb3
    %c100_i32 = arith.constant {handshake.name = "constant14"} 100 : i32
    %c3_i32 = arith.constant {handshake.name = "constant15"} 3 : i32
    %c1_i32_1 = arith.constant {handshake.name = "constant16"} 1 : i32
    %15 = arith.addi %14, %c3_i32 {dynamatic.predict = {location = "end", marker = 0 : i32, type = "", values = ""}, dynamatic.predict.result_idx = 0 : i32, handshake.name = "addi3"} : i32
    %16 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %17 = arith.index_cast %16 {handshake.name = "index_cast1"} : i64 to index
    memref.store %15, %arg0[%17] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : memref<100xi32>
    %18 = arith.addi %0, %c1_i32_1 {handshake.name = "addi4"} : i32
    %19 = arith.cmpi ult, %18, %c100_i32 {handshake.name = "cmpi3"} : i32
    cf.cond_br %19, ^bb1(%18 : i32), ^bb5 {handshake.name = "cond_br1"}
  ^bb5:  // pred: ^bb4
    return {handshake.name = "return0"}
  }
}

