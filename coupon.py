# Exact calculation of probability getting at least one ball in each of m bins after tossing n balls
# Given parameters:
# - m = max_m: maximum value for number of balls tossed
# - n = max_n: maximum value for number of bins
# - i = print_interval: interval for printing results
# Usage: python3 coupon.py -m 500 -n 8500 -i 500
#
# Uses formula from Concrete Mathematics p. 583 exercise 8.38 for probability of first getting at least one ball in each bin at exactly n tosses:
# prob_first_at_n = m^(-n) * m! * sn2(n-1, m-1)
# where sn2(n, m) is a stirling number of the second type and equals the number of ways to partition n identifieable objects into m nonempty subsets.
# sn2(0, 0) = 1 (by convention)
# sn2(n, 0) = 0 for n >= 1
# sn2(n, m) = 0 for m > n
# For 1 <= m <= n:
# sn2(n, m) = m * sn2(n-1, m) + sn2(n-1, m-1)
#
# to avoid underflow/overflow, calculate scaled stirling numbers, ssn(n, m), defined as:
# ssn(n, m) = sn2(n, m) / (m+1)^(n-m)
# 
# Note:
# ssn(0, 0) = 1
# ssn(n, 0) = 0 for n >= 1
# ssn(n, m) = 0 for m > n
# For 1 <= m <= n:
# ssn(n-1, m) = sn2(n-1, m) / (m+1)^(n-m-1)
# sn2(n-1, m) = ssn(n-1, m) * (m+1)^(n-m-1)
# ssn(n-1, m-1) = sn2(n-1, m-1) / m^(n-m)
# sn2(n-1, m-1) = ssn(n-1, m-1) * m^(n-m)
# sn2(n, m) = (m+1)^(n-m) * ssn(n, m)
# 
# ssn(n, m) = sn2(n, m) / (m+1)^(n-m)
#           = (m * sn2(n-1, m) + sn2(n-1, m-1)) / (m+1)^(n-m)
#           = sn2(n-1, m) * m / (m+1)^(n-m) + sn2(n-1, m-1) / (m+1)^(n-m)
#           = ssn(n-1, m) * (m+1)^(n-m-1) * m / (m+1)^(n-m) + ssn(n-1, m-1) * m^(n-m) / (m+1)^(n-m)
#           = ssn(n-1, m) * (m/(m+1)) + ssn(n-1, m-1) * (m/(m+1))^(n-m)
#           = (m/(m+1)) * ssn(n-1, m) + (m/(m+1))^(n-m) * ssn(n-1, m-1)
#
#
# Let mterm(m) = m!/m^m
#
# Note:
# prob_first_at_n = m^(-m) * m! * sn2(n-1, m-1)/m^(n-m) = mterm(m) * ssn(n-1, m-1)

import sys
import math
import numpy as np
import argparse

def mterm(m):					# m!/m^m
  m_term = 1.0					
  for i in range(1, m+1):
    m_term *= float(i)/float(m)
  return m_term

class Ssn(object):				# scaled stirling numbers of the second type
  def __init__(self,
               max_n,				# maximum number of items
               max_m):				# maximum number of nonempty subsets
    self.max_n = max_n
    self.max_m = max_m
    new_values = [1.0]				# create row of new values for case n = 0
    for m in range(1, self.max_m+1):
      new_values.append(0.0)
    self.value = [new_values]			# self.value[n][m] = ssn(n, m)
    for n in range(1, self.max_n+1):
      prev_values = new_values			# prev_values are values for row n-1
      new_values = [0.0]			# values for "cur_n" items
      for m in range(1, self.max_m+1):
        new_values.append((float(m)/float(m+1)) * prev_values[m] + (float(m)/float(m+1))**(n-m) * prev_values[m-1])
      self.value.append(new_values)

  def get_value(self, n, m):			# return sn2(n, m)
    assert 0 <= n <= self.max_n
    assert 0 <= m <= self.max_m
    return self.value[n][m]

class ProbFilled(object):			# probability that all m buckets are filled with n balls
  def __init__(self,
               max_n,				# max_number of balls
               max_m):				# max_number of buckets
    self.max_n = max_n
    self.max_m = max_m
    self.s = Ssn(self.max_n-1, self.max_m-1)	# prob[n][m] = mterm(m) * s.get_value(n-1, m-1)
    self.prob = [[0.0]]				# initialize self.prob[n][m] to 0.0
    for n in range(1, self.max_n+1):
      self.prob.append([0.0])
    for n in range(self.max_n+1):
      for m in range(1, self.max_m+1):
        self.prob[n].append(0.0)
    self.cum_prob = [[0.0]]			# initialize self.cum_prob[n][m] to 0.0
    for n in range(1, self.max_n+1):
      self.cum_prob.append([0.0])
    for n in range(self.max_n+1):
      for m in range(1, self.max_m+1):
        self.cum_prob[n].append(0.0)
    for m in range(1, self.max_m+1):
      for n in range(1, self.max_n+1):
        self.prob[n][m] = mterm(m) * self.s.get_value(n-1, m-1)
      self.cum_prob[0][m] = self.prob[0][m]
      for n in range(1, self.max_n+1):
        self.cum_prob[n][m] = self.cum_prob[n-1][m] + self.prob[n][m]

  def get_prob(self, n, m):			# return prob[n][m]
    assert 0 <= n <= self.max_n
    assert 0 <= m <= self.max_m
    return self.prob[n][m]

  def get_cum_prob(self, n, m):			# return cum_prob[n][m]
    assert 0 <= n <= self.max_n
    assert 0 <= m <= self.max_m
    return self.cum_prob[n][m]

# Main program
parser = argparse.ArgumentParser(description='Calculate probability of getting at least one ball in each of m bins after tossing n balls')
parser.add_argument('-m', dest='max_m', help='maximum number of bins')
parser.add_argument('-n', dest='max_n', help='maximum number of balls')
parser.add_argument('-i', dest='print_interval', help='prints values where n is a multiple of i')
args = parser.parse_args()
max_m = int(args.max_m)
max_n = int(args.max_n)
print_interval = int(args.print_interval)
p = ProbFilled(max_n, max_m)
m = max_m
for n in range(1, max_n+1):
  if ((n % print_interval) == 0):
    print('m:', m, 'n:', n, 'prob:', p.get_prob(n, m), 'cum_prob:', p.get_cum_prob(n, m))
