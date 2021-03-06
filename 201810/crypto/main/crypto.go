package main

import (
  "os"
  "net"
  "fmt"
  "time"
  "math/rand"
)

// checck errors
func check(err error) {
  if err != nil {
    panic(err)
  }
}

// read 680 random bytes
func getBlock() ([]byte) {
  f, err := os.Open("/dev/urandom")
  check(err)
  block := make([]byte, 680)
  count, err := f.Read(block)
  check(err)
  if count != 680 {
    panic("cannot read bytes")
  }
  f.Close()
  return block
}

// mix in flag
func mix(block []byte, secret string) ([]byte) {
  rand.Seed(time.Now().UTC().UnixNano())
  offset := rand.Intn(20) * 34
  for i := 0; i < 34; i ++ {
    block[offset + i] = block[offset + i] ^ secret[i]
  }
  return block
}

// handle in new thread
func handleConnection(conn net.Conn, block []byte, flag string) {
  for {
    time.Sleep(1000 * 1000 * 100)
    conn.Write(mix(block, flag))

    // wait
    resp := make([]byte, 1)
    conn.Read(resp)
  }
}

// entry point
func main() {
  // get flag
  flag := os.Getenv("CRYPTO_FLAG")
  if len(flag) == 0 {
    fmt.Println("Please set the CRYPTO_FLAG environmental variable")
    os.Exit(-1)
  }

  // set-up socket
  service := ":1812"
  tcpAddr, err := net.ResolveTCPAddr("tcp4", service)
  check(err)
  listener, err := net.ListenTCP("tcp", tcpAddr)
  check(err)

  // listen
  for {
    conn, err := listener.Accept()
    if err != nil {
      continue
    }
    block := getBlock()
    go handleConnection(conn, block, flag)
  }
}
