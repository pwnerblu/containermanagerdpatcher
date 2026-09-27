# containermanagerdpatcher
Patch containermanagerd so iOS 8.x will boot on iOS 10.3.3 SEP without seprmvr64

DISCLAIMER: The patcher itself is written with AI, but I have 100% tested this patcher myself and I've confirmed it working on iPhone 5S, iOS 8.0 and managed to boot iOS 8.0 on 10.3.3 OTA SEP.

# How to compile:

`gcc containermanagerdpatcher.c -o containermanagerdpatcher`

# Usage:

`./containermanagerdpatcher containermanagerd containermanagerd.patch`
