#!/usr/bin/env python

import codecs
from bitcoin.rpc import Proxy

if __name__ == '__main__':
    url      = raw_input('Please enter the RPC url: ')
    username = raw_input('Please enter the RPC username: ')
    password = raw_input('Please enter the RPC password: ')
    
    proxy = Proxy(url, username, password)
    numblocks = proxy.getblockcount() + 1

    fp = codecs.open('out.csv', 'w', 'utf-8')

    for idx in xrange(numblocks):
        blockinfo = proxy.getblock(proxy.getblockhash(idx))
        fp.write(','.join(map(str, [
            blockinfo['height'],
            blockinfo['time'],
            blockinfo['difficulty'],
        ]))+'\n')
    
    fp.close()