# Calculates the parameters for a burn depot as a function of given parameters.
# Given parameters:
# - u = gr_u (GrU in paper): security against griefing by the users
# - o = gr_o (GrO in paper): security against griefing by the operator
# - d = depot_value (D in paper): value of burn depot (in sats)
# - a = max_active_channels (MaxA in paper): maximum number of active channels
# - b = hit_bound: upper bound on maximum number of expected hits
# - m = min_sale_frac (MinSaleFrac in paper): minimum fraction of max_active_channels O must sell
# Calculated parameters:
# - min_frac_loss_u (MinFracLossU in paper): security against griefing by the users
# - max_frac_loss_u (MaxFracLossU in paper): security against griefing by the operator
# - prime (P in paper): number of values for each target (required to be a prime)
# - max_h (MaxH in paper): maximum number of expected hits
# - min_burn_per_channel: minimum expected amount burned per channel
# - max_burn_per_channel: maximum expected amount burned per channel
# - burn_uncertainty_frac: uncertainty of expected amount burned per channel divided by minimum expected amount burned per channel
# - match_u: matching value (in sats) provided by user for each sat of uncertainty in expected burn amount
# - match_o: matching value (in sats) provided by operator for each sat of uncertainty in expected burn amount
# - match_s: matching value (in sats) provided by user plus operator for each sat of uncertainty in expected burn amount
# - match_c: matching value (in # of matching channels) provided by user plus operator for each sat of uncertainty in expected burn amount
# Usage:
# python3 burn_depot.py -u 0.30 -o 0.05 -d 1000003 -a 1000003 -b 1.0 -m 0.90
# python3 burn_depot.py -u 0.25 -o 0.10 -d 1000003 -a 1000003 -b 1.5 -m 0.90

import sys
import argparse
import math

class Security(object):
  def __init__(self,				# depot security object
               gr_u,				# security against griefing by the users
               gr_o):				# security against griefing by the operator
    self.gr_u = gr_u
    self.gr_o = gr_o
    self.min_frac_loss_u = self.gr_u/(1.0 + self.gr_u)
    self.max_frac_loss_u = 1.0/(1.0 + self.gr_o)
    self.match_u = self.max_frac_loss_u*self.min_frac_loss_u/(self.max_frac_loss_u - self.min_frac_loss_u)
    self.match_o = (1.0 - self.max_frac_loss_u)*self.min_frac_loss_u/(self.max_frac_loss_u - self.min_frac_loss_u)
    self.match_s = self.match_u + self.match_o

  def get_match_u(self):			# Return the factor by which each sat of uncertainty is multiplied to obtain the user's matching funds (in sats)
    return self.match_u

  def get_match_o(self):			# Return the factor by which each sat of uncertainty is multiplied to obtain the operator's matching funds (in sats)
    return self.match_o

  def get_match_s(self):			# Return the factor by which each sat of uncertainty is multiplied to obtain the user's plus operator's matching funds (in sats)
    return self.match_s

  def get_gr_u(self):
    return self.gr_u

  def get_gr_o(self):
    return self.gr_o

  def get_min_frac_loss_u(self):
    return self.min_frac_loss_u

  def get_max_frac_loss_u(self):
    return self.max_frac_loss_u

class BurnDepot(object):
  def __init__(self,				# depot object
               security,			# security object for given depot
               depot_value,			# value of burn depot (in sats)
               max_active_channels,		# maximum number of active channels
               hit_bound,			# upper bound on maximum number of expected hits
               min_sale_frac):			# minimum fraction of max_active_channels O must sell
    self.security = security
    self.depot_value = depot_value
    self.max_active_channels = max_active_channels
    self.hit_bound = hit_bound
    self.min_sale_frac = min_sale_frac
    self.min_active_channels = math.ceil(min_sale_frac*max_active_channels)
    self.prime = self.calc_prime()
    self.max_h = self.max_active_channels/self.prime
    self.min_h = self.min_active_channels/self.prime

  def is_prime(self, n):			# returns True iff n is a prime
    if (n % 2 == 0):
      return False
    divisor = 3
    while (divisor*divisor <= n):
      if (n % divisor == 0):
        return(False)
      divisor += 2
    return True

  def calc_prime(self):				# return smallest prime such that prime >= max_active_channels/security.get_upper_bound_max_h() (which implies max_active_channels/prime <= security.get_upper_bound_max_h())
    n = math.ceil(self.max_active_channels/self.hit_bound)
    while (not self.is_prime(n)):
      n += 1
    return n

  def b(self, h):				# return (e^h - 1 - h/2)/(h*e^h)
    return (math.exp(h) - 1 - (h/2))/(h*math.exp(h))

  def get_security(self):
    return self.security

  def get_max_active_channels(self):
    return self.max_active_channels

  def get_prime(self):
    return self.prime

  def get_max_h(self):
    return self.max_h

  def get_min_h(self):
    return self.min_h

  def get_min_burn_per_channel(self):
    return self.b(self.max_h)*self.depot_value/self.prime

  def get_max_burn_per_channel(self):
    return self.b(self.min_h)*self.depot_value/self.prime

  def get_burn_uncertainty_frac(self):
    return (self.get_max_burn_per_channel() - self.get_min_burn_per_channel())/self.get_min_burn_per_channel()

  def get_match_c(self):
    return self.security.get_match_s()/self.get_min_burn_per_channel()


# Main program
parser = argparse.ArgumentParser(description='Calculate depot parameters as a function of given parameters)')
parser.add_argument('-u', dest='gr_u', help='security against griefing by the users')
parser.add_argument('-o', dest='gr_o', help='security against griefing by the operator')
parser.add_argument('-d', dest='depot_value', help='total value of burn depot (in sats) ')
parser.add_argument('-a', dest='max_active_channels', help='maximum number of active channels')
parser.add_argument('-b', dest='hit_bound', help='upper bound on maximum number of expected hits')
parser.add_argument('-m', dest='min_sale_frac', help='minimum fraction of max_active_channels O must sell')
args = parser.parse_args()
gr_u = float(args.gr_u)
assert gr_u >= 0
gr_o = float(args.gr_o)
assert gr_o >= 0
assert gr_u*gr_o < 1
depot_value = int(args.depot_value)
assert depot_value > 0
max_active_channels = int(args.max_active_channels)
assert max_active_channels > 0
hit_bound = float(args.hit_bound)
assert hit_bound > 0.0
min_sale_frac = float(args.min_sale_frac)
assert min_sale_frac > 0.0
assert min_sale_frac <= 1.0

security = Security(gr_u, gr_o)
depot = BurnDepot(security, depot_value, max_active_channels, hit_bound, min_sale_frac)

print('Input parameters: gr_u:', gr_u, 'gr_o:', gr_o, 'depot_value:', depot_value, 'max_active_channels:', max_active_channels, 'hit_bound:', hit_bound, 'min_sale_frac:', min_sale_frac)
print('Outputs: min_frac_loss_u: %8.6f' % security.get_min_frac_loss_u(), 'max_frac_loss_u: %8.6f' % security.get_max_frac_loss_u(), 'prime:', depot.get_prime(), 'max_h: %8.6f' % depot.get_max_h(), 'min_h: %8.6f' % depot.get_min_h())
print('min_burn_per_channel: %8.6f' % depot.get_min_burn_per_channel(), 'max_burn_per_channel: %8.6f' % depot.get_max_burn_per_channel(), 'burn_uncertainty_frac: %8.6f' % depot.get_burn_uncertainty_frac())
print('match_u: %8.6f' % security.get_match_u(), 'match_o: %8.6f' % security.get_match_o(), 'match_s: %8.6f' % security.get_match_s(), 'match_c: %8.6f' % depot.get_match_c())
