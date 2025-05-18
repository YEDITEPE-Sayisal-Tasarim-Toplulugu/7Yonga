import sys
import time
import serial
import select
import argparse
import msvcrt
import serial.tools.list_ports

LINSTENER_BRATE = 9600
LINSTENER_PORT  = "COM4"
LINSTENER_MOD   = "decimal"
LINSTENER_BYTES = 1

parser = argparse.ArgumentParser()
parser.add_argument('--port', dest='port', type=str, help='port: device port name')
parser.add_argument('--brate', dest='brate', type=int, help='brate: connection baud rate')
parser.add_argument('--mod', dest='mod', type=str, help='write_delay: delay value per byte')
parser.add_argument('--byte_count', dest='bytecount', type=int, help='write_delay: delay value per byte')
args = parser.parse_args()

LINSTENER_BRATE = args.brate if (args.brate is not None) else LINSTENER_BRATE
LINSTENER_PORT = args.port if (args.port is not None) else LINSTENER_PORT
LINSTENER_MOD = args.mod if (args.mod is not None) else LINSTENER_MOD
LINSTENER_BYTES = args.bytecount if (args.bytecount is not None) else LINSTENER_BYTES

print("UART LISTINIG START (press x to exit)...")

try:
    ser = serial.Serial(LINSTENER_PORT, LINSTENER_BRATE)
    
    while True:
        if msvcrt.kbhit():
            char = msvcrt.getch()
            if char.decode() == "x":
                break
        
        if ser.in_waiting:
            bytes_value = ser.read(LINSTENER_BYTES)

            if LINSTENER_MOD == "decimal":
                print(int.from_bytes(bytes_value, sys.byteorder), end="\n")
            elif LINSTENER_MOD == "ascii":
                print(str(chr), end="")
            else:
                print(f"ERROR: LINSTENER_MOD: {LINSTENER_MOD} (decimal/ascii)")

    ser.close()
except Exception as connection_er:
    print("connection error:", str(connection_er))