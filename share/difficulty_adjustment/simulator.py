#!/usr/bin/env python
# -*- coding: utf-8 -*-

FILTER_COEFF = [
     -845859,  -459003,  -573589,  -703227,  -848199, -1008841, 
    -1183669, -1372046, -1573247, -1787578, -2011503, -2243311, 
    -2482346, -2723079, -2964681, -3202200, -3432186, -3650186, 
    -3851924, -4032122, -4185340, -4306430, -4389146, -4427786, 
    -4416716, -4349289, -4220031, -4022692, -3751740, -3401468, 
    -2966915, -2443070, -1825548, -1110759,  -295281,   623307, 
     1646668,  2775970,  4011152,  5351560,  6795424,  8340274, 
     9982332, 11717130, 13539111, 15441640, 17417389, 19457954, 
    21554056, 23695744, 25872220, 28072119, 30283431, 32493814, 
    34690317, 36859911, 38989360, 41065293, 43074548, 45004087, 
    46841170, 48573558, 50189545, 51678076, 53028839, 54232505, 
    55280554, 56165609, 56881415, 57422788, 57785876, 57968085, 
    57968084, 57785876, 57422788, 56881415, 56165609, 55280554, 
    54232505, 53028839, 51678076, 50189545, 48573558, 46841170, 
    45004087, 43074548, 41065293, 38989360, 36859911, 34690317, 
    32493814, 30283431, 28072119, 25872220, 23695744, 21554057, 
    19457953, 17417389, 15441640, 13539111, 11717130,  9982332, 
     8340274,  6795424,  5351560,  4011152,  2775970,  1646668, 
      623307,  -295281, -1110759, -1825548, -2443070, -2966915, 
    -3401468, -3751740, -4022692, -4220031, -4349289, -4416715, 
    -4427787, -4389146, -4306430, -4185340, -4032122, -3851924, 
    -3650186, -3432186, -3202200, -2964681, -2723079, -2482346, 
    -2243311, -2011503, -1787578, -1573247, -1372046, -1183669, 
    -1008841,  -848199,  -703227,  -573589,  -459003,  -845858]

from itertools import izip
def next_difficulty(history, gain, limiter):
    if len(history)<2:
        return 1.0

    vTimeDelta = [x[0] for x in history[:145]]
    vTimeDelta = [y-x for x,y in izip(vTimeDelta[:-1], vTimeDelta[1:])]
    vTimeDelta.extend([600] * (144 - len(vTimeDelta)))
    vTimeDelta = [x*y for x,y in izip(vTimeDelta, FILTER_COEFF)]

    # TODO: remove FPU arithmetic and replace with bignums
    dFilteredInterval = -sum(vTimeDelta) / 2147483648.0;
    dAdjustmentFactor = 1.0 - gain * (dFilteredInterval - 600.0) / 600.0;
    #print (dFilteredInterval, dAdjustmentFactor)
    
    max_limiter = limiter
    min_limiter = 1.0 / limiter
    if dAdjustmentFactor > max_limiter:
        dAdjustmentFactor = max_limiter
    elif dAdjustmentFactor < min_limiter:
        dAdjustmentFactor = min_limiter
    
    return history[0][1] * dAdjustmentFactor

from random import expovariate
def simulate(start, end, nethash, interval=72, gain=0.18, limiter=2.0):
    blocks = []
    time = start
    while time < end:
        if not len(blocks)%interval:
            nd = next_difficulty(blocks[:-146:-1], gain, limiter)
        blocks.append( (round(time), nd) )
        nh = nethash(time)
        time += expovariate(1.0 / (600.0 * nd / nh))
        #print (nd, nh, time)
    return blocks

from bisect import bisect_left
def smooth(history, window=16):
    # Sort the history by time, so that we don't have any negative block
    # times. Not ideal, but allows us to avoid possible instability in the
    # simulator.
    history = [(int(n),int(t),float(d))
               for t,n,d in sorted((t,n,d) for n,t,d in history)]
    diff = []
    for idx in xrange(2, len(history)-1):
        offset = min(idx-1, window, len(history)-1-idx)
        interval = (history[idx + offset][1] -
                    history[idx - offset][1]) / (2.0 * offset + 1)
        diff.append((history[idx][1], history[idx][2]*600.0/interval))
    def nethash(time):
        if  time > diff[-1][0]:
            return diff[-1][1]
        return diff[bisect_left(diff, (time, 1.0))][1]
    return nethash

from csv import reader
def history_from_csv(filename):
    with open(filename, 'r') as csvfile:
        return [(int(n),int(t),float(d)) for n,t,d in reader(csvfile)]

def utility_function(blocks):
    # Calculate root-mean-square difference from a straight-line
    # approximation
    l = len(blocks)
    b = sum(t for t,d in blocks)/l - 300.0*l
    e = sum((600.0*n+b - t)**2 for n,(t,d) in enumerate(blocks))/l
    return e**0.5

def xfrange(x, y, step):
    while x < y:
        yield x
        x += step

if __name__ == '__main__':
    frc = history_from_csv('frc.csv')
    print(u"Freicoin historical error: %f" % utility_function([(t,d) for n,t,d in frc]))

    btc = history_from_csv('btc.csv')
    print(u"Bitcoin historical error: %f" % utility_function([(t,d) for n,t,d in btc]))
    smoothed = smooth(btc)
    print(u"w=12,G=0.15")
    fp = open('out.csv', 'w')
    for l in xfrange(1.0175, 1.25, 0.0025):
    #for I in xrange(1, 73):
        blks = simulate(btc[0][1], btc[-1][1], smoothed, interval=12, gain=0.15, limiter=l)
        quality = (l, utility_function(blks))
        print(u"l=%f: %f" % quality)
        fp.write("%f,%f\n" % quality)
    fp.close()

#
# End of File
#
