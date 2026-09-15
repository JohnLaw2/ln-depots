# Calculates the parameters for a Lightning depot as a function of given parameters.
# Given parameters:
# - u = gr_u (GrU in paper): security against griefing by the users
# - o = gr_o (GrO in paper): security against griefing by the operator
# - r = balance_range: minimum value of ratio max_b(au, max_au)/min_b(au) (optional with default value of 1.5)
# - n = number_of_users (n in paper): number of users using the depot (used to calculate average channel allocation per user)
# - a = max_active_channels (MaxA in paper): maximum number of active channels
# - c = max_cumulative_channels (MaxC in paper): maximum cumulative number of channels created over the lifetime of the depot
# - s = supported_user_balances: lower bound on value (in sats) that can be sold to users
# - e = example_flag: if True print example sends and receives (optional with default value of False)
# - p = # of random payments (sends or receives)
# - q = seed for randomness
# - z = allocation for random user
# - f = factor controlling random payment sizes (random payments change balance by a factor of at most 1.0 + f)
# Calculated parameters:
# - min_frac_loss_u (MinFracLossU in paper): security against griefing by the users
# - max_frac_loss_u (MaxFracLossU in paper): security against griefing by the operator
# - prime (P in paper): number of values for each target (required to be a prime)
# - max_h (MaxH in paper): maximum number of expected hits
# - targets (h in paper): number of targets
# - depot_value (D in paper): value of depot (in sats)
# - utilization: (value that can be sold to users)/depot_value
# Usage:
# (to print depot parameters and failure to drain analysis only): python3 depot.py -u 0.30 -o 0.05 -r 1.5 -n 1000000 -a 10000000 -c 1000000000 -s 100000000 
# (to include example sends and receives): python3 depot.py -u 0.30 -o 0.05 -r 1.5 -n 1000000 -a 10000000 -c 1000000000 -s 100000000 -e True
# (with random user payments): python3 depot.py -u 0.30 -o 0.05 -r 1.5 -n 1000000 -a 10000000 -c 1000000000 -s 100000000 -p 100000 -z 10
# (with high griefer penalization parameters): python3 depot.py -u 0.50 -o 0.10 -r 1.5 -n 1000000 -a 10000000 -c 1000000000 -s 100000000 -p 100000 -z 10
# (with constrained random user payments): python3 depot.py -u 0.50 -o 0.10 -r 1.5 -n 1000000 -a 10000000 -c 1000000000 -s 100000000 -p 100000 -q 1407748 -z 10 -f 0.5

# Note: All depot Lightning channel payments are in integral numbers of sats, while all depot balances are in integral numbers of 1/P sats.
# Depot balances are printed out both as integers in terms of 1/P-sat units and as floating point values in terms of sat units

# Limitations:
# * This program only supports a single send or receive at a time. In order to support multiple simultaneous payments, it would be necessary to associate each burn amount with a specific payment.

import sys
import argparse
import math
import random

PRECISION = 0.00000000000001			# required precision when calculating values using binary search
G_SECURITY_BITS = 512				# the parameter g is selected such that P^g >= 2^G_SECURITY_BITS
BURN_BUFFER = 10				# buffer to tolerate round-off error and to ensure minimum operator balance for burn contributions (expressed in units of 1/P sats)
ZERO_HITS_ON_CHAIN_TX = 2			# number of on-chain transactions when there are 0 hits (Funding + Target)
ONE_HIT_ON_CHAIN_TX = 6				# number of on-chain transactions when there is exactly 1 hit (Funding + Target + Hit + Claim + Commitment + user's tx spending their Lightning payout))
TWO_PLUS_HITS_ON_CHAIN_TX = 5			# number of on-chain transactions when there are 2+ hits (Funding + Target + Hit + Burn of Hit output 0 + Burn of Hit output 1))


class Security(object):
  def __init__(self,				# depot security object
               gr_u,				# security against griefing by the users
               gr_o,				# security against griefing by the operator
               balance_range):			# minimum value of ratio max_b(au, max_au)/min_b(au)
    self.gr_u = gr_u
    self.gr_o = gr_o
    self.balance_range = balance_range
    self.min_frac_loss_u = self.gr_u/(1.0+self.gr_u)
    self.max_frac_loss_u = 1.0/(1.0+self.gr_o)
    assert balance_range < self.max_frac_loss_u/self.min_frac_loss_u
    self.upper_bound_max_h = self.calc_upper_bound_max_h()

  def g(self, x):				# (e^x - 1 - x)/(e^x - 1)
    return (math.exp(x)-1-x)/(math.exp(x)-1)

  def calc_upper_bound_max_h(self):		# Return largest max_h (to within PRECISION) such that max_b(max_active_channels, max_active_channels)/min_b(max_active_channels) >= balance_range,
						# that is, return the largest number of expected hits assuming all max_active_channels channels are allocated to a single user who has all max_active_channels channels active.
						# This value will then be used to calculate prime, given the formula prime = max_active_channels/max_h, which implies
						# min_b(max_active_channels) = depot_value*max_active_channels*min_frac_loss_u*max_h/(2*max_active_channels) = depot_value*min_frac_loss_u*max_h/2 and
						# max_b(max_active_channels, max_active_channels) = depot_value*max_frac_loss_u*g(max_h) so
						# max_b(max_active_channels, max_active_channels)/min_b(max_active_channels) = max_frac_loss_u*g(max_h)*2/(min_frac_loss_u*max_h)
    min_bound = 0.0				# low end of range of possible values for upper_bound_max_h
    max_bound = 2.0/self.min_frac_loss_u	# high end of range of poassible values for upper_bound_max_h
						# note max_frac_loss_u < 1 and g(x) < 1 so max_b(max_active_channels, max_active_channels)/min_b(max_active_channels) < 2/(min_frac_loss_u*max_h),
						# so setting max_h to 2/min_frac_loss_u yields 2/((min_frac_loss_u*max_h) = 1 <= balance_range.
    assert self.max_frac_loss_u*self.g(max_bound)*2.0/(self.min_frac_loss_u*max_bound) <= 1.0
    while (max_bound - min_bound > PRECISION):	# perform binary search
      mid = (min_bound+max_bound)/2.0
      if (self.max_frac_loss_u*self.g(mid)*2.0/(self.min_frac_loss_u*mid) > self.balance_range):
        min_bound = mid
      else:
        max_bound = mid
    assert self.max_frac_loss_u*self.g(min_bound)*2.0/(self.min_frac_loss_u*min_bound) >= self.balance_range
    return min_bound

  def get_payment_scale_factor(self):		# Return the factor by which each payment is scaled in order to include matching funds from both parties
    return 1.0/(self.max_frac_loss_u - self.min_frac_loss_u)

  def get_u_match_factor(self):			# Return the factor by which each payment is multiplied to obtain the user's matching funds
    return self.get_payment_scale_factor()*self.get_min_frac_loss_u()

  def get_o_match_factor(self):			# Return the factor by which each payment is multiplied to obtain the operator's matching funds
    return self.get_payment_scale_factor()*(1.0 - self.get_max_frac_loss_u())

  def get_match_factor(self):			# Return the factor by which each payment is multiplied to obtain the user's plus operator's matching funds
    return self.get_u_match_factor() + self.get_o_match_factor()

  def get_gr_u(self):
    return self.gr_u

  def get_gr_o(self):
    return self.gr_o

  def get_balance_range(self):
    return self.balance_range

  def get_min_frac_loss_u(self):
    return self.min_frac_loss_u

  def get_max_frac_loss_u(self):
    return self.max_frac_loss_u

  def get_upper_bound_max_h(self):
    return self.upper_bound_max_h


class Depot(object):
  def __init__(self,				# depot object
               security,			# security object for given depot
               max_active_channels,		# maximum number of active channels
               max_cumulative_channels,		# maximum cumulative number of channels created over the lifetime of the depot
               supported_user_balances):	# lower bound on value (in sats) that can be sold to users
    self.security = security
    self.max_active_channels = max_active_channels
    self.max_cumulative_channels = max_cumulative_channels
    self.supported_user_balances = supported_user_balances
    self.prime = self.calc_prime()
    self.max_h = self.max_active_channels/self.prime
    self.targets = self.calc_num_targets()
						# fraction of depot's value that can be sold to users
    self.max_utilization = self.security.get_max_frac_loss_u()*self.security.g(self.max_h)
						# depot's value in sats, which must be an even number so that each output of Hit transaction can hold exactly half of the depot's value
    self.depot_value = math.ceil(self.supported_user_balances/self.max_utilization)
    if (self.depot_value % 2 == 1):
      self.depot_value += 1
						# maximum balance for users assuming all max_active_channels channels are allocated to a single user who has all max_active_channels channels active.
    self.max_b = math.floor(self.depot_value*self.max_utilization)
						# max expected value of the sum of all outputs of the latest Commitment transaction for a single active channel in the depot
						# expressed in units of 1/P sats (where P = self.prime)
    self.channel_value = int(self.depot_value/2)
						# minimum value of user's channel balance to prevent users' failure-to-drain attack
    self.u_channel_min = math.ceil(self.depot_value*self.security.get_min_frac_loss_u()/2)
						# minimum value of operator's channel balance to prevent operator from stealing the Hit transaction's output 1 by using an Arbtrary (Arb) transaction
    self.o_channel_min = math.ceil(self.depot_value*(1.0 - security.get_max_frac_loss_u())/2.0)

  def is_prime(self, n):			# returns True iff n is a prime
    if (n % 2 == 0):
      return False
    divisor = 3
    while (divisor*divisor <= n):
      if (n % divisor == 0):
        return False
      divisor += 2
    return True

  def calc_prime(self):				# return smallest prime such that prime >= max_active_channels/security.get_upper_bound_max_h() (which implies max_active_channels/prime <= security.get_upper_bound_max_h())
    n = math.ceil(self.max_active_channels/self.security.get_upper_bound_max_h())
    while (not self.is_prime(n)):
      n += 1
    return n

  def calc_num_targets(self):			# return required number of targets given required number of cumulative channels created over the lifetime of the depot
    prime = self.prime
    channels_per_target = prime-1		# fewer than prime channels is guaranteed to leave at least 1 of prime target values a miss
    if (self.prime >= 1000):			# the following results come from boundcoupon.py and guarantee at most a 10^-30 chance of having all target values for one target be hits
      channels_per_target = 2*prime
    if (self.prime >= 2000):
      channels_per_target = 3*prime
    if (self.prime >= 4000):
      channels_per_target = 4*prime
    if (self.prime >= 11000):
      channels_per_target = 5*prime
    if (self.prime >= 28000):
      channels_per_target = 6*prime
    if (self.prime >= 76000):
      channels_per_target = 7*prime
    if (self.prime >= 287000):
      channels_per_target = 8*prime
    if (self.prime >= 562000):
      channels_per_target = 9*prime
    if (self.prime >= 1529000):
      channels_per_target = 10*prime
    if (self.prime >= 4159000):
      channels_per_target = 11*prime
    if (self.prime >= 11310000):
      channels_per_target = 12*prime
    if (self.prime >= 30760000):
      channels_per_target = 13*prime
    if (self.prime >= 83657000):
      channels_per_target = 14*prime
    if (self.prime >= 227517000):
      channels_per_target = 15*prime
    if (self.prime >= 618148000):
      channels_per_target = 16*prime
    if (self.prime >= 1681135000):
      channels_per_target = 17*prime
    return math.ceil(self.max_cumulative_channels/channels_per_target)

  def calc_min_b(self, au):			# return minimum user balance assuming user has au active channels
    if (au == 0):
      return 0
    else:
      return int(au)*self.u_channel_min

  def calc_min_b_no_burn(self, au):		# return minimum user balance when no user funds are being burned
    if (au == 0):
      return 0
    else:					# include enough free user funds (beyond per-channel minima) to burn matching funds for revocation of one channel
      return int(au)*self.u_channel_min + math.ceil(self.u_channel_min*self.security.get_u_match_factor())

  def calc_max_b(self, au, max_au):		# return maximum user balance assuming user has au active channels and max_au allocated channels
    if (au == 0):
      return 0
    return math.floor(self.depot_value*self.security.get_max_frac_loss_u()*max_au*self.security.g(au*self.max_h/max_au)*self.prime/(self.max_active_channels))

  def calc_max_c(self, au, max_au):		# return maximum capacity for channel au assuming user has max_au allocated channels
    assert au >= 1
    assert au <= max_au
    if (au == 1):
      return self.calc_max_b(au, max_au)
    else:					# ensure u_channel_min requirement is met
      return max(self.u_channel_min, self.calc_max_b(au, max_au) - self.calc_max_b(au-1, max_au))

  def calc_min_nza(self, max_au):		# return minimum nonzero number of active channels required to hold user's balance assuming user has max_au allocated channels
    if (max_au == 1):				# allocation of 1 channel elimiinates need to acquire or revoke channels (other than fund or drain operation)
      return 1
    acquire_min_bound = max_au			# minimum number of channels required to acquire minimum balance in one additional channel when holding maximum balance in acquire_min_bound channels
    for channel_num in range(1, max_au):
      channel_num_ok = True
						# verify that channel_num channels can hold no-burn balance for channel_num+1 channels (so no gaps in user's allowable balance)
      if (self.calc_min_b_no_burn(channel_num+1) > self.calc_max_b(channel_num, max_au) - BURN_BUFFER):
        channel_num_ok = False
						# verify that channel_num channels can hold sufficient user free funds for user to acquire another channel
      if (self.calc_max_b(channel_num, max_au) - channel_num*self.u_channel_min < math.ceil(self.u_channel_min*(1.0 + self.security.get_u_match_factor())) + BURN_BUFFER):
        channel_num_ok = False
						# verify that channel_num channels can hold sufficient operator free funds for user to acquire another channel
      if (channel_num*(self.get_channel_value() - self.o_channel_min) - self.calc_max_b(channel_num, max_au) < math.ceil(self.u_channel_min*self.security.get_o_match_factor()) + BURN_BUFFER):
        channel_num_ok = False
      if (channel_num_ok):
        acquire_min_bound = channel_num
        break
    return acquire_min_bound

  def calc_min_a(self, balance, max_au):	# return minimum number of active channels required to hold user's balance assuming user has max_au allocated channels
    if (balance == 0):
      return 0
    assert balance <= self.calc_max_b(max_au, max_au)
    for channel_num in range(1, max_au+1):
      if (balance <= self.calc_max_b(channel_num, max_au)):
        return channel_num

  def calc_max_a(self, balance, max_au):	# return maximum number of active channels that can hold user's balance assuming user has max_au allocated channels
    if (balance == 0):
      return 0
    assert balance >= self.calc_min_b_no_burn(1)
    for channel_num in range(max_au, -1, -1):
      if (balance >= self.calc_min_b_no_burn(channel_num)):
        return channel_num

						# return minimum number of active channels required to hold user's free balance (above per-channel minimum) assuming user has max_au allocated channels (or 1 if free_balance == 0)
  def calc_min_free_a(self, free_balance, max_au):
    if (free_balance == 0):
      return 1
    for channel_num in range(1, max_au+1):
      if (free_balance <= self.calc_max_b(channel_num, max_au) - channel_num*self.u_channel_min):
        return channel_num
    return max_au + 1                           # impossible to hold given free balance

  def get_security(self):
    return self.security

  def get_max_active_channels(self):
    return self.max_active_channels

  def get_max_cumulative_channels(self):
    return self.max_cumulative_channels

  def get_supported_user_balances(self):
    return self.supported_user_balances

  def get_prime(self):
    return self.prime

  def get_max_h(self):
    return self.max_h

  def get_targets(self):
    return self.targets

  def get_max_utilization(self):
    return self.max_utilization

  def get_depot_value(self):
    return self.depot_value

  def get_channel_value(self):
    return self.channel_value

  def get_u_channel_min(self):
    return self.u_channel_min

  def get_o_channel_min(self):
    return self.o_channel_min

  def get_max_b(self):
    return self.max_b

  def get_g(self):				# return smallest value of g such that prime^g >= 2^G_SECURITY_BITS
    return math.ceil(G_SECURITY_BITS*math.log(2)/math.log(self.prime))

def zero_hit_prob(h):				# return probability that a depot will have exactly 0 hits given h expected hits
  return 1.0/math.exp(h)			# 1/e^h is Poisson approximation for probability of exactly 0 events given h expected events

def one_hit_prob(h):				# return probability that a depot will have exactly 1 hit given h expected hits
  return h/math.exp(h)				# h/e^h is Poisson approximation for probability of exactly 1 event given h expected events

def burn_prob(h):				# return probability that a depot will have 2+ hits and thus be burned given h expected hits
  return (math.exp(h)-1-h)/math.exp(h)		# (e^h - 1 - h)/e^h is Poisson approximation for probability of 2+ events given h expected events


class Channel(object):
  def __init__(self,				# depot active channel object
               depot,				# depot containing the channel
               channel_num,			# number of this channel, starting with 1 which indicates user's oldest channel
               allocation,			# number of channels allocated to user
               u_balance):			# max expected value of user's output of latest Commitment transaction for this channel (in units of 1/P sats)
    self.depot = depot
               					# max expected value of sum of all outputs of latest Commitment transaction for this channel (in units of 1/P sats)
    self.channel_value = depot.get_channel_value()
    self.channel_num = channel_num
    assert self.channel_num >= 1
    self.allocation = allocation
    assert self.allocation >= self.channel_num
    self.u_min = depot.get_u_channel_min()
    self.o_min = depot.get_o_channel_min()
						# calculate user's maximum balance in this channel
    self.u_max = self.depot.calc_max_c(self.channel_num, self.allocation)
    self.u_balance = u_balance
    assert self.u_balance >= self.u_min
    assert self.u_balance <= self.u_max
						# max expected value of operator's output of latest Commitment transaction for this channel
    self.o_balance = self.channel_value - u_balance
    assert self.o_balance >= self.o_min
    self.u_burn = 0				# max expected value of user's contribution to burn output of latest Commitment transaction for this channel
    self.o_burn = 0				# max expected value of operator's contribution to burn output of latest Commitment transaction for this channel

  def add_u_burn(self, amount):			# move given amount from user's balance to user's burn contribution
    assert amount >= 0
    assert self.u_balance >= amount + self.u_min
    self.u_balance -= amount
    self.u_burn += amount

  def add_o_burn(self, amount):			# move given amount from operator's balance to operator's burn contribution
    assert amount >= 0
    assert self.o_balance >= amount + self.o_min
    self.o_balance -= amount
    self.o_burn += amount

  def remove_u_burn(self, amount):		# move given amount from user's burn contribution to user's balance
    assert amount >= 0
    assert self.u_burn >= amount
    assert self.u_balance + amount <= self.u_max
    self.u_burn -= amount
    self.u_balance += amount

  def remove_o_burn(self, amount):		# move given amount from operator's burn contribution to operator's balance
    assert amount >= 0
    assert self.o_burn >= amount
    self.o_burn -= amount
    self.o_balance += amount

  def transfer_u2o(self, amount):		# transfer given amount from user's burn contribution to operator's burn contribution
    assert amount >= 0
    assert self.u_burn >= amount
    self.u_burn -= amount
    self.o_burn += amount

  def transfer_o2u(self, amount):		# transfer given amount from operator's burn contribution to user's burn contribution
    assert amount >= 0
    assert self.o_burn >= amount
    self.o_burn -= amount
    self.u_burn += amount

  def get_transferable_o2u(self):		# return largest amount that operator can contribute to burn output which can then be transferred to user
    user_max_receive = self.u_max - self.u_balance - self.u_burn
    return min(user_max_receive, self.o_balance - self.o_min)

  def get_transferable_u2o(self):		# return largest amount that user can contribute to burn output which can then be transferred to operator
    return self.u_balance - self.u_min

  def get_depot(self):
    return self.depot

  def get_channel_num(self):
    return self.channel_num

  def get_allocation(self):
    return self.allocation

  def get_u_max(self):
    return self.u_max

  def get_o_min(self):
    return self.o_min

  def get_u_balance(self):
    return self.u_balance

  def get_u_burn(self):
    return self.u_burn

  def get_u_min(self):
    return self.u_min

  def get_o_min(self):
    return self.o_min

  def get_o_balance(self):
    return self.o_balance

  def get_o_burn(self):
    return self.o_burn

  def get_u_burnable(self):
    return self.u_balance - self.depot.get_u_channel_min()

  def get_o_burnable(self):
    return self.o_balance - self.depot.get_o_channel_min()

  def get_channel_value(self):
    return self.channel_value

  def get_channel_burn(self):
    return self.u_burn + self.o_burn

  def print_balances(self,
                     channel_id,		# position of channel in user's list of active channels, indexed starting with 1
                     in_sats):			# flag which is True iff balances should be printed using sat units (and thus as floating point values) rather than in 1/P-sat units (and thus as integers)
    if (in_sats):
      p = float(self.depot.get_prime())
      sat_capacity = self.depot.calc_max_c(channel_id, self.allocation)/p
      sat_u_min = self.get_u_min()/p
      sat_o_min = self.get_o_min()/p
      sat_user = self.get_u_balance()/p
      sat_user_burn = self.get_u_burn()/p
      sat_channel_burn = self.get_channel_burn()/p
      sat_operator_burn = self.get_o_burn()/p
      sat_operator = self.get_o_balance()/p
      sat_channel = self.get_channel_value()/p
      print('id: %3d' % channel_id, '(Balances in sats) user_min: %9.3f' % sat_u_min, 'capacity: %9.3f' % sat_capacity, 'user: %9.3f' % sat_user, 'user_burn: %9.3f' % sat_user_burn, 'channel_burn: %9.3f' % sat_channel_burn,\
            'operator_burn: %9.3f' % sat_operator_burn, 'operator: %9.3f' % sat_operator, 'operator_min: %9.3f' % sat_o_min, 'channel: %9.3f' % sat_channel)
    else:
      print('id: %3d' % channel_id, '(Balances in 1/P-sats) user_min: %11d' % self.u_min, 'capacity: %11d' % self.depot.calc_max_c(channel_id, self.allocation), 'user: %11d' % self.get_u_balance(), 'user_burn: %11d' % self.get_u_burn(),\
            'channel_burn: %11d' % self.get_channel_burn(), 'operator_burn: %11d' %self.get_o_burn(), 'operator: %11d' % self.get_o_balance(), 'operator_min: %11d' % self.o_min, 'channel: %11d' % self.get_channel_value())

class User(object):
  def __init__(self,				# depot user object
               depot,				# depot used by this user
               allocation):			# number of channels in depot allocated to this user
    self.depot = depot
    self.allocation = allocation
    self.channels = [] 				# list of active channels owned by this user
    security = self.depot.get_security()
    self.min_nza = self.depot.calc_min_nza(allocation)
						# verify that user's minimum balance does not exceed user's maximum balance
    if (self.calc_min_fund() > depot.calc_max_b(allocation, allocation)):
      print('ERROR: User minimum balance:', self.calc_min_fund(), 'exceeds user maximum balance:', depot.calc_max_b(allocation, allocation))
    assert self.calc_min_fund() <= depot.calc_max_b(allocation, allocation)
						# track send, receive, channel acquisitions and channel update statistics
    self.sends = 0
    self.atomic_sends = 0
    self.receives = 0
    self.atomic_receives = 0
    self.cumulative_channels = 0		# cumulative number of channel acquisitions
    self.channel_updates = 0			# cumulative number of channel updates

  def get_balance(self):
    balance = 0
    for channel in self.channels:
      balance += channel.u_balance
    return balance

  def get_u_burn(self):
    burn = 0
    for channel in self.channels:
      burn+= channel.u_burn
    return burn

  def get_o_burn(self):
    burn = 0
    for channel in self.channels:
      burn+= channel.o_burn
    return burn

  def get_depot(self):
    return self.depot

  def get_allocation(self):
    return self.allocation

  def get_num_channels(self):
    return len(self.channels)

  def get_channels(self):
    return self.channels

  def get_min_nza(self):
    return self.min_nza

  def calc_min_fund(self):			# return minimum balance to fund user, which equals minimum user balance when user has minimum number of active channels and is not allocating any funds to a burn output
    return self.depot.calc_min_b_no_burn(self.min_nza)

  def fund(self, 				# given a new user with no active channels, fund that user with the given amount
           amount,				# amount to fund expressed as an integer number of 1/P-sats
           print_flag):				# print updates if print_flag == True
    sat_amount = amount/float(self.depot.get_prime())
    if (print_flag):
      print('***** FUND with', sat_amount, 'sats equals', amount, '1/P-sats')
    assert self.get_num_channels() == 0
    depot = self.depot
    allocation = self.allocation
    assert amount >= self.calc_min_fund()
    assert amount <= depot.calc_max_b(allocation, allocation)
    u_channel_min = depot.get_u_channel_min()
						# calculate number of channels required to fund given amount
    num_channels = depot.calc_min_a(amount, allocation)
						# allocate minimum balance per channel
    amount -= num_channels*u_channel_min
						# allocate remaining free balance across channels
    for cur_channel in range(1, num_channels+1):
      max_free = depot.calc_max_c(cur_channel, allocation) - u_channel_min
      if (max_free < amount):
        channel_amount = u_channel_min + max_free
        amount -= max_free
      else:
        channel_amount = u_channel_min + amount
        amount = 0
      self.channels.append(Channel(depot, cur_channel, allocation, channel_amount))
      self.cumulative_channels += 1
      self.channel_updates += 1
    if (print_flag):
      self.print_user()
    else:
      self.check_user()

  def acquire_channel(self):				# user acquires one new channel with minimum user balance
      self.channels.append(Channel(self.depot, self.get_num_channels()+1, self.allocation, self.depot.get_u_channel_min()))
      self.cumulative_channels += 1
      self.channel_updates += 1

  def revoke_channel(self):				# user revokes newest channel with minimum user balance
      last_channel = self.channels.pop()
      assert last_channel.get_u_balance() == self.depot.get_u_channel_min()

  def move_to_burn(self,				# move given amounts from user's and operator's balances to burn outputs, assuming no burn amounts currently exist
                   u_add_to_burn,			# list of per-channel amounts to move from user's balances to burn outputs
                   o_add_to_burn,			# list of per-channel amounts to move from operator's balances to burn outputs
                   print_flag):				# print updates if print_flag == True
    security = self.depot.get_security()
    channels = self.get_channels()
    num_channels = len(channels)
    u_burn_required = sum(u_add_to_burn)
    o_burn_required = sum(o_add_to_burn)
    burn_required = u_burn_required + o_burn_required
    burned = 0
    while (burned < burn_required):
      found_channel = False				# have not yet found the channel to update
      for cur_channel in range(num_channels):
							# first, try to burn entire remaining required amounts for cur_channel
        u_channel_burn = u_add_to_burn[cur_channel] - channels[cur_channel].get_u_burn()
        o_channel_burn = o_add_to_burn[cur_channel] - channels[cur_channel].get_o_burn()
							# now reduce burn amounts as required to keep the user's and operator's burn contributions within required balance
        if ((self.get_o_burn() + o_channel_burn)/security.get_gr_o() < self.get_u_burn() + u_channel_burn):
          u_channel_burn = max(0, math.floor((self.get_o_burn() + o_channel_burn)/security.get_gr_o() - self.get_u_burn()))
        if ((self.get_u_burn() + u_channel_burn)/security.get_gr_u() < self.get_o_burn() + o_channel_burn):
          o_channel_burn = max(0, math.floor((self.get_u_burn() + u_channel_burn)/security.get_gr_u() - self.get_o_burn()))
        if (u_channel_burn > 0):
							# tolerate roundoff error
          while (float(self.get_u_burn() + u_channel_burn)/float(self.get_u_burn() + self.get_o_burn() + u_channel_burn + o_channel_burn) > security.get_max_frac_loss_u() and u_channel_burn > 0):
            u_channel_burn -= 1
        if (u_channel_burn > 0):
          channels[cur_channel].add_u_burn(u_channel_burn)
          burned += u_channel_burn
          found_channel = True
        if (o_channel_burn > 0):
							# tolerate roundoff error
          while (float(self.get_u_burn())/float(self.get_u_burn() + self.get_o_burn() + o_channel_burn) < security.get_min_frac_loss_u() and o_channel_burn > 0):
            o_channel_burn -= 1
        if (o_channel_burn > 0):
          channels[cur_channel].add_o_burn(o_channel_burn)
          burned += o_channel_burn
          found_channel = True
        if (found_channel):
          if (print_flag):
            self.print_user()
          else:
            self.check_user()
          self.channel_updates += 1
          break
      assert found_channel

  def move_from_burn(self,				# move all burn amounts from burn outputs to user's and operator's outputs
                     print_flag):			# print updates if print_flag == True
    security = self.depot.get_security()
    channels = self.get_channels()
    num_channels = len(channels)
    u_burn = self.get_u_burn()
    o_burn = self.get_o_burn()
    burned = u_burn + o_burn
    while (burned > 0):
      u_single_burn_channels = 0			# number of channels in which only the user burns funds
      o_single_burn_channels = 0			# number of channels in which only the operator burns funds
      dual_burn_channels = 0				# number of channels in which both parties contribute burn funds
      found_channel = False				# have not yet found the channel to update
      for cur_channel in range(num_channels):		# if possible, unburn in a channel where only one party has a burn contribution (thus saving channels with 2-party burn contributions for last)
        u_channel_unburn = channels[cur_channel].get_u_burn()
        o_channel_unburn = channels[cur_channel].get_o_burn()
        if (u_channel_unburn > 0 and o_channel_unburn > 0):
          dual_burn_channels += 1
          continue					# skip this channel for now as both parties have a burn contribution
        if (u_channel_unburn > 0):
          u_single_burn_channels += 1
        if (o_channel_unburn > 0):
          o_single_burn_channels += 1
							# reduce unburn amounts as required to keep the user's and operator's burn contributions within required balance
        if ((o_burn - o_channel_unburn)/security.get_gr_o() < u_burn - u_channel_unburn):
          o_channel_unburn = math.floor(o_burn - security.get_gr_o()*(u_burn - u_channel_unburn))
                                                        # tolerate roundoff error
        if (burned - o_channel_unburn - u_channel_unburn > 0):
          while (float(u_burn - u_channel_unburn)/float(burned - o_channel_unburn - u_channel_unburn) > security.get_max_frac_loss_u()):
            o_channel_unburn -= 1
        if ((u_burn - u_channel_unburn)/security.get_gr_u() < o_burn - o_channel_unburn):
          u_channel_unburn = math.floor(u_burn - security.get_gr_u()*(o_burn - o_channel_unburn))
                                                        # tolerate roundoff error
          if (burned - o_channel_unburn - u_channel_unburn > 0):
            while (float(u_burn - u_channel_unburn)/float(burned - o_channel_unburn - u_channel_unburn) < security.get_min_frac_loss_u()):
              u_channel_unburn -= 1
        if (u_channel_unburn > 0):
          channels[cur_channel].remove_u_burn(u_channel_unburn)
          u_burn -= u_channel_unburn
          burned -= u_channel_unburn
          found_channel = True
        if (o_channel_unburn > 0):
          channels[cur_channel].remove_o_burn(o_channel_unburn)
          o_burn -= o_channel_unburn
          burned -= o_channel_unburn
          found_channel = True
        if (found_channel):
          if (print_flag):
            self.print_user()
          else:
            self.check_user()
          self.channel_updates += 1
          break
      if (not found_channel):				# not able to unburn in a channel where only one party has a burn contribution
        for cur_channel in range(num_channels):
          u_channel_unburn = channels[cur_channel].get_u_burn()
          o_channel_unburn = channels[cur_channel].get_o_burn()
							# reduce unburn amounts as required to keep the user's and operator's burn contributions within required balance
          if ((o_burn - o_channel_unburn)/security.get_gr_o() < u_burn - u_channel_unburn):
            o_channel_unburn = math.floor(o_burn - security.get_gr_o()*(u_burn - u_channel_unburn))
                                                        # tolerate roundoff error
          if (burned - o_channel_unburn - u_channel_unburn > 0):
            while (float(u_burn - u_channel_unburn)/float(burned - o_channel_unburn - u_channel_unburn) > security.get_max_frac_loss_u()):
              o_channel_unburn -= 1
          if ((u_burn - u_channel_unburn)/security.get_gr_u() < o_burn - o_channel_unburn):
            u_channel_unburn = math.floor(u_burn - security.get_gr_u()*(o_burn - o_channel_unburn))
                                                        # tolerate roundoff error
          if (burned - o_channel_unburn - u_channel_unburn > 0):
            while (float(u_burn - u_channel_unburn)/float(burned - o_channel_unburn - u_channel_unburn) < security.get_min_frac_loss_u()):
              u_channel_unburn -= 1
          if (u_channel_unburn > 0):
							# prevent the user's unburn in the only dual-burn channel if the user has burn funds in other single-burn channel(s)
            if (dual_burn_channels == 1 and u_single_burn_channels > 0):
              u_channel_unburn = 0
							# limit the user's unburn in this channel if required to support efficient unburning of the operator's funds in other single-burn channel(s)
            if (dual_burn_channels == 1 and o_single_burn_channels > 0):
              u_channel_unburn = min(u_channel_unburn, channels[cur_channel].get_u_burn() - math.ceil(o_burn*security.get_gr_u()))
							# tolerate roundoff error
            if (burned - o_channel_unburn - u_channel_unburn > 0):
              while (float(u_burn - u_channel_unburn)/float(burned - o_channel_unburn - u_channel_unburn) < security.get_min_frac_loss_u()):
                u_channel_unburn -= 1
            if ((o_burn - o_channel_unburn)/security.get_gr_o() < u_burn - u_channel_unburn):
              o_channel_unburn = math.floor(o_burn - security.get_gr_o()*(u_burn - u_channel_unburn))
                                                        # tolerate roundoff error
            if (burned - o_channel_unburn - u_channel_unburn > 0):
              while (float(u_burn - u_channel_unburn)/float(burned - o_channel_unburn - u_channel_unburn) > security.get_max_frac_loss_u()):
                o_channel_unburn -= 1
          if (o_channel_unburn > 0):
							# prevent the operator's unburn in the only dual-burn channel if the operator has burn funds in other single-burn channel(s)
            if (dual_burn_channels == 1 and o_single_burn_channels > 0):
              o_channel_unburn = 0
							# limit the operator's unburn in this channel if required to support efficient unburning of the user's funds in other single-burn channel(s)
            if (dual_burn_channels == 1 and u_single_burn_channels > 0):
              o_channel_unburn = min(o_channel_unburn, channels[cur_channel].get_o_burn() - math.ceil(u_burn*security.get_gr_o()))
                                                        # tolerate roundoff error
            if (burned - o_channel_unburn - u_channel_unburn > 0):
              while (float(u_burn - u_channel_unburn)/float(burned - o_channel_unburn - u_channel_unburn) > security.get_max_frac_loss_u()):
                o_channel_unburn -= 1
            if ((u_burn - u_channel_unburn)/security.get_gr_u() < o_burn - o_channel_unburn):
              u_channel_unburn = math.floor(u_burn - security.get_gr_u()*(o_burn - o_channel_unburn))
							# tolerate roundoff error
            if (burned - o_channel_unburn - u_channel_unburn > 0):
              while (float(u_burn - u_channel_unburn)/float(burned - o_channel_unburn - u_channel_unburn) < security.get_min_frac_loss_u()):
                u_channel_unburn -= 1
          if (u_channel_unburn > 0):
            channels[cur_channel].remove_u_burn(u_channel_unburn)
            u_burn -= u_channel_unburn
            burned -= u_channel_unburn
            found_channel = True
          if (o_channel_unburn > 0):
            channels[cur_channel].remove_o_burn(o_channel_unburn)
            o_burn -= o_channel_unburn
            burned -= o_channel_unburn
            found_channel = True
          if (found_channel):
            if (print_flag):
              self.print_user()
            else:
              self.check_user()
            break
            self.channel_updates += 1
      assert found_channel

  def partition_transfer_to_user(self,			# partitions given amount being transferred from operator to user (via burn outputs) across channels
                                 amount,		# amount being transferred to user due to a receive or a channel revocation
                                 revoke_num,		# number of channels being revoked (= 0 for a receive)
                                 transfer_funds,	# per-channel list of funds being transferred from operator to user (via burn outputs)
                                 u_add_to_burn,		# per-channel list of matching funds provided by user
                                 o_add_to_burn):	# per-channel list of matching funds provided by operator
    depot = self.get_depot()
    security = depot.get_security()
    allocation = self.get_allocation()
    channels = self.get_channels()
    num_channels = self.get_num_channels()
    u_channel_min = depot.get_u_channel_min()
    start_balance = self.get_balance()
    start_free_balance = start_balance - num_channels*u_channel_min
							# number of channels holding user's free funds (beyond per-channel minimum) at start of transfer
    start_channel = depot.calc_min_free_a(start_free_balance, allocation)
    end_balance = start_balance + amount
    end_free_balance = end_balance - num_channels*u_channel_min
							# number of channels holding user's free funds (beyond per-channel minimum) at end of transfer
    end_channel = depot.calc_min_free_a(end_free_balance, allocation)
							# lowest user's balance during the transfer
							# amount is increased by 1 to avoid unbalanced rounding of matching funds
    low_balance = start_balance - math.ceil(security.get_u_match_factor()*(amount+1))
    low_free_balance = low_balance - num_channels*u_channel_min
							# number of channels holding user's free funds (beyond per-channel minimum) when they are lowest during transfer
    low_channel = depot.calc_min_free_a(low_free_balance, allocation)
							# determine which funds from which channels will be burned during the transfer
							# first, determine which funds from which channels will be burned by the operator to fund the transfer
    to_be_transferred = amount
    for cur_channel in range(start_channel-1, end_channel):
      channel_transfer_amount = min(channels[cur_channel].get_transferable_o2u(), to_be_transferred)
      transfer_funds[cur_channel] = channel_transfer_amount
      to_be_transferred -= channel_transfer_amount
							# second, determine which matching funds from which channels will be burned by the user during the transfer
							# the user's matching funds are taken from the user's youngest channels
    to_be_matched = math.ceil(security.get_u_match_factor()*(amount+1))
    for cur_channel in range(start_channel-1, low_channel-2, -1):
      channel_match_amount = min(channels[cur_channel].get_u_balance() - u_channel_min, to_be_matched)
      u_add_to_burn[cur_channel] = channel_match_amount
      to_be_matched -= channel_match_amount
							# third, determine which matching funds from which channels will be burned by the operator during the transfer
    for x in range(num_channels):
      o_add_to_burn[x] = transfer_funds[x]
    to_be_matched = math.ceil(security.get_o_match_factor()*(amount+1))
							# the operator's matching funds are taken from low_channel through end channel in equal amounts (to the extent that is possible)
    for cur_channel in range(low_channel-1, end_channel):
      remaining_channels = end_channel - cur_channel	# number of channels from cur_channel through end_channel, inclusive
      channel_match_amount = min(channels[cur_channel].get_o_balance() - channels[cur_channel].get_o_min() - o_add_to_burn[cur_channel], math.ceil(float(to_be_matched)/remaining_channels))
      o_add_to_burn[cur_channel] += channel_match_amount
      to_be_matched -= channel_match_amount
							# the operator's remaining matching funds are taken starting from low_channel and then increasingly younger channels (cyclically, restarting from the oldest unrevoked channel, if needed)
    cur_channel = low_channel-1
    while (to_be_matched > 0):
      channel_match_amount = min(channels[cur_channel].get_o_balance() - channels[cur_channel].get_o_min() - o_add_to_burn[cur_channel], to_be_matched)
      o_add_to_burn[cur_channel] += channel_match_amount
      to_be_matched -= channel_match_amount
      cur_channel += 1
      if (cur_channel == num_channels - revoke_num):
        cur_channel = 0

  def atomic_receive(self,				# atomically receive given amount
                     amount,
                     print_flag):			# print updates if print_flag == True
    depot = self.get_depot()
    security = depot.get_security()
    allocation = self.get_allocation()
    channels = self.get_channels()
    num_channels = self.get_num_channels()
    u_channel_min = depot.get_u_channel_min()
    self.atomic_receives += 1
    if (print_flag):
      p = self.depot.get_prime()
      print('***** ATOMIC RECEIVE', amount/p, 'sats equals', amount, '1/P-sats')
    assert amount > 0
    transfer_funds = [0 for x in range(num_channels)] 	# transfer_funds[] partitions the value being received across channels
    u_add_to_burn = [0 for x in range(num_channels)] 	# u_add_to_burn[] partitions the user's matching funds across channels
    o_add_to_burn = [0 for x in range(num_channels)] 	# o_add_to_burn[] partitions the operator's transfer and matching funds across channels
    self.partition_transfer_to_user(amount, 0, transfer_funds, u_add_to_burn, o_add_to_burn)
							# move funds from user's and operator's balances to burn outputs in a series of single-channel updates that maintains sufficiently balanced burn amounts between the user and the operator
    self.move_to_burn(u_add_to_burn, o_add_to_burn, print_flag)
    for cur_channel in range(num_channels): 		# transfer operator's burn contribution for receive amount to user's burn contribution (signifying that the operator has received the funds over Lightning)
      if (transfer_funds[cur_channel] > 0):
        channel_transfer = transfer_funds[cur_channel]
        channels[cur_channel].transfer_o2u(channel_transfer)
    if (print_flag):
      self.print_user()
    else:
      self.check_user()
    self.move_from_burn(print_flag) 			# move funds from burn outputs to user's and operator's outputs in a series of single-channel updates that maintains sufficiently balanced burn amounts between the user and the operator

  def atomic_revoke(self,				# atomically revoke a single channels with minimum user balance
                    print_flag):			# print updates if print_flag == True
    depot = self.get_depot()
    security = depot.get_security()
    allocation = self.get_allocation()
    channels = self.get_channels()
    num_channels = self.get_num_channels()
    u_channel_min = depot.get_u_channel_min()
    amount = u_channel_min 				# amount user will receive in channels that remain after revocation of one channel
    if (print_flag):
      p = self.depot.get_prime()
      print('***** REVOKE one channel with:', amount/p, 'sats equals', amount, '1/P-sats')
    assert amount > 0
    transfer_funds = [0 for x in range(num_channels)] 	# transfer_funds[] partitions the value being received across channels
    u_add_to_burn = [0 for x in range(num_channels)] 	# u_add_to_burn[] partitions the user's matching funds across channels
    o_add_to_burn = [0 for x in range(num_channels)] 	# o_add_to_burn[] partitions the operator's transfer and matching funds across channels
    self.partition_transfer_to_user(amount, 1, transfer_funds, u_add_to_burn, o_add_to_burn)
							# move funds from user's and operator's balances to burn outputs in a series of single-channel updates that maintains sufficiently balanced burn amounts between the user and the operator
    self.move_to_burn(u_add_to_burn, o_add_to_burn, print_flag)
    self.revoke_channel()
    need_to_transfer = u_channel_min
    for cur_channel in range(num_channels - 1):
      if (transfer_funds[cur_channel] > 0 and need_to_transfer > 0):
        channel_transfer = transfer_funds[cur_channel]
        if (channel_transfer > need_to_transfer):
          channel_transfer = need_to_transfer
        channels[cur_channel].transfer_o2u(channel_transfer)
        transfer_funds[cur_channel] -= channel_transfer
        need_to_transfer -= channel_transfer
    if (print_flag):
      self.print_user()
    else:
      self.check_user()
    self.move_from_burn(print_flag) 			# move funds from burn outputs to user's and operator's outputs in a series of single-channel updates that maintains sufficiently balanced burn amounts between the user and the operator

  def calc_largest_atomic_receive(self,			# return value of largest possible atomic receive given specified number of active channels
                                  num_active):		# number of active channels used for atomic receive
    depot = self.get_depot()
    security = depot.get_security()
    allocation = self.get_allocation()
    start_b = self.get_balance()
    u_match_factor = security.get_u_match_factor()
    o_match_factor = security.get_o_match_factor()
    channel_value = depot.get_channel_value()
    operator_channel_min = depot.get_o_channel_min()
    min_b_allowed = depot.calc_min_b(num_active)
    max_b_allowed = depot.calc_max_b(num_active, allocation)
    min_b_payment_bound = math.floor(float((start_b - min_b_allowed))/u_match_factor)
    max_b_payment_bound = max_b_allowed - start_b
							# limit payment size to ensure operator has sufficient balance to burn payment and operator's matching funds for payment
    operator_payment_bound = math.floor(float((num_active*(channel_value - operator_channel_min) - start_b))/(1.0 + o_match_factor))
                                                        # include "- 2" term due to rouding up of user's and operator's match amounts
    return min(min_b_payment_bound, max_b_payment_bound, operator_payment_bound) - 2

  def receive(self,					# perform requested payment to user, return True iff successful
             amount,					# value of payment in 1/P-sats
             can_be_divided,				# flag indicating whether or not the payment can be divided into multiple Lightning payments, each with their own receipt
             print_flag):				# print updates if print_flag == True
    self.receives += 1
    sat_amount = amount/float(self.depot.get_prime())
    if (print_flag):
      print('***** RECEIVE', sat_amount, 'sats equals', amount, '1/P-sats')
    depot = self.get_depot()
    security = depot.get_security()
    allocation = self.get_allocation()
    channels = self.get_channels()
    u_channel_min = depot.get_u_channel_min()
    while (amount > 0):
      num_active = len(channels)
      start_b = self.get_balance()
							# determine if payment can be performed with current number of active channels
      payment_bound = self.calc_largest_atomic_receive(num_active)
      atomic_num_active = num_active
      if (amount <= payment_bound):			# payment can be performed with current number of active channels
        atomic_amount = amount
      else: 						# payment cannot be performed with current number of active channels
        atomic_amount = payment_bound
        cur_active = num_active 			# try larger numbers of active channels
        while (cur_active <= depot.calc_max_a(start_b, allocation)):
          cur_bound = self.calc_largest_atomic_receive(cur_active)
          if (cur_bound > payment_bound):
            atomic_num_active = cur_active
            if (amount <= cur_bound):			# payment can be performed with given number of active channels
              atomic_amount = amount
              break
            else:
              atomic_amount = cur_bound
          cur_active += 1
        cur_active = num_active				# try smaller numbers of active channels
        while (cur_active >= depot.calc_min_a(start_b, allocation) and cur_active >= self.get_min_nza()):
          cur_bound = self.calc_largest_atomic_receive(cur_active)
          if (cur_bound > payment_bound):
            atomic_num_active = cur_active
            if (amount <= cur_bound):			# payment can be performed with given number of active channels
              atomic_amount = amount
              break
            else:
              atomic_amount = cur_bound
          cur_active -= 1
      if (atomic_amount < amount and not can_be_divided):
        return False
							# get required number of active channels for first atomic payment
      if (num_active > atomic_num_active):
        need_to_revoke = num_active - atomic_num_active
        while (need_to_revoke > 0):
          need_to_revoke -= 1
          self.atomic_revoke(print_flag)
      if (num_active < atomic_num_active):
        need_to_acquire = atomic_num_active - num_active
        while (need_to_acquire > 0):
          need_to_acquire -= 1
          self.atomic_acquire(print_flag)
							# perform atomic receive
      self.atomic_receive(atomic_amount, print_flag)
      amount -= atomic_amount
    return True

  def partition_transfer_from_user(self,		# partitions given amount being transferred from user to operator (via burn outputs) across channels
                                   amount,		# amount being transferred to operator due to a send or a channel acquisition
                                   transfer_funds,	# per-channel list of funds being transferred from user to operator (via burn outputs)
                                   u_add_to_burn,	# per-channel list of matching funds provided by user
                                   o_add_to_burn):	# per-channel list of matching funds provided by operator
    depot = self.get_depot()
    security = depot.get_security()
    allocation = self.get_allocation()
    channels = self.get_channels()
    num_channels = self.get_num_channels()
    u_channel_min = depot.get_u_channel_min()
    start_balance = self.get_balance()
    start_free_balance = start_balance - num_channels*u_channel_min
							# number of channels holding user's free funds (beyond per-channel minimum) at start of transfer
    start_channel = depot.calc_min_free_a(start_free_balance, allocation)
    end_balance = start_balance - amount
    end_free_balance = end_balance - num_channels*u_channel_min
							# number of channels holding user's free funds (beyond per-channel minimum) at end of transfer
    end_channel = depot.calc_min_free_a(end_free_balance, allocation)
							# lowest user's balance during the transfer
							# amount is increased by 1 to avoid unbalanced rounding of matching funds
    low_balance = end_balance - math.ceil(security.get_u_match_factor()*(amount+1))
    low_free_balance = low_balance - num_channels*u_channel_min
							# number of channels holding user's free funds (beyond per-channel minimum) when they are lowest during transfer
    low_channel = depot.calc_min_free_a(low_free_balance, allocation)
							# determine which funds from which channels will be burned during the transfer
							# first, determine which funds from which channels will be burned by the user to fund the transfer
							# transfer_funds[] partitions the value being transferred across channels
    to_be_transferred = amount
    for cur_channel in range(start_channel-1, end_channel-2, -1):
      channel_transfer_amount = min(channels[cur_channel].get_transferable_u2o(), to_be_transferred)
      transfer_funds[cur_channel] = channel_transfer_amount
      to_be_transferred -= channel_transfer_amount
							# second, determine which matching funds from which channels will be burned by the user during the transfer
    for x in range(num_channels):
      u_add_to_burn[x] = transfer_funds[x]
							# the user's matching funds are taken from the user's youngest channels
    to_be_matched = math.ceil(security.get_u_match_factor()*(amount+1))
    for cur_channel in range(end_channel-1, low_channel-2, -1):
      channel_match_amount = min(channels[cur_channel].get_u_balance() - u_add_to_burn[cur_channel] - u_channel_min, to_be_matched)
      u_add_to_burn[cur_channel] += channel_match_amount
      to_be_matched -= channel_match_amount
							# third, determine which matching funds from which channels will be burned by the operator during the transfer
							# o_add_to_burn[] partitions the operator's matching funds across channels
    to_be_matched = math.ceil(security.get_o_match_factor()*(amount+1))
							# the operator's matching funds are taken from low_channel through start channel in equal amounts (to the extent that is possible)
    for cur_channel in range(low_channel-1, start_channel):
      remaining_channels = start_channel - cur_channel	# number of channels from cur_channel through start_channel, inclusive
      channel_match_amount = min(channels[cur_channel].get_o_balance() - channels[cur_channel].get_o_min(), math.ceil(float(to_be_matched)/remaining_channels))
      o_add_to_burn[cur_channel] = channel_match_amount
      to_be_matched -= channel_match_amount
							# the operator's remaining matching funds are taken starting from low_channel and then increasingly younger channels (cyclically, restarting from the oldest channel, if needed)
    cur_channel = low_channel-1
    while (to_be_matched > 0):
      channel_match_amount = min(channels[cur_channel].get_o_balance() - channels[cur_channel].get_o_min() - o_add_to_burn[cur_channel], to_be_matched)
      o_add_to_burn[cur_channel] += channel_match_amount
      to_be_matched -= channel_match_amount
      cur_channel += 1
      if (cur_channel == num_channels):
        cur_channel = 0

  def atomic_send(self,					# atomically send given amount
                  amount,
                  print_flag):				# print updates if print_flag == True
    depot = self.get_depot()
    security = depot.get_security()
    allocation = self.get_allocation()
    channels = self.get_channels()
    num_channels = self.get_num_channels()
    u_channel_min = depot.get_u_channel_min()
    self.atomic_sends += 1
    if (print_flag):
      p = self.depot.get_prime()
      print('***** ATOMIC SEND', amount/p, 'sats equals', amount, '1/P-sats')
    assert amount > 0
    transfer_funds = [0 for x in range(num_channels)] 	# transfer_funds[] partitions the value being received across channels
    u_add_to_burn = [0 for x in range(num_channels)] 	# u_add_to_burn[] partitions the user's matching funds across channels
    o_add_to_burn = [0 for x in range(num_channels)] 	# o_add_to_burn[] partitions the operator's transfer and matching funds across channels
    self.partition_transfer_from_user(amount, transfer_funds, u_add_to_burn, o_add_to_burn)
							# move funds from user's and operator's balances to burn outputs in a series of single-channel updates that maintains sufficiently balanced burn amounts between the user and the operator
    self.move_to_burn(u_add_to_burn, o_add_to_burn, print_flag)
    for cur_channel in range(num_channels): 		# transfer user's burn contribution for send amount to operator's burn contribution (signifying that the operator has sent the funds over Lightning)
      if (transfer_funds[cur_channel] > 0):
        channel_transfer = transfer_funds[cur_channel]
        channels[cur_channel].transfer_u2o(channel_transfer)
    if (print_flag):
      self.print_user()
    else:
      self.check_user()
    self.move_from_burn(print_flag) 			# move funds from burn outputs to user's and operator's outputs in a series of single-channel updates that maintains sufficiently balanced burn amounts between the user and the operator

  def atomic_acquire(self,				# atomically acquire a single channel with minimum user balance
                     print_flag):			# print updates if print_flag == True
    depot = self.get_depot()
    security = depot.get_security()
    allocation = self.get_allocation()
    channels = self.get_channels()
    num_channels = self.get_num_channels()
    u_channel_min = depot.get_u_channel_min()
    amount = u_channel_min 				# amount user will lose
    if (print_flag):
      p = self.depot.get_prime()
      print('***** ACQUIRE one channel with:', amount/p, 'sats equals', amount, '1/P-sats')
    assert amount > 0
    transfer_funds = [0 for x in range(num_channels)] 	# transfer_funds[] partitions the value being received across channels
    u_add_to_burn = [0 for x in range(num_channels)] 	# u_add_to_burn[] partitions the user's matching funds across channels
    o_add_to_burn = [0 for x in range(num_channels)] 	# o_add_to_burn[] partitions the operator's transfer and matching funds across channels
    self.partition_transfer_from_user(amount, transfer_funds, u_add_to_burn, o_add_to_burn)
							# move funds from user's and operator's balances to burn outputs in a series of single-channel updates that maintains sufficiently balanced burn amounts between the user and the operator
    self.move_to_burn(u_add_to_burn, o_add_to_burn, print_flag)
    self.acquire_channel()
    self.channel_updates += 1			# each newly-acquired channel requires signatures from U and O
    need_to_transfer = u_channel_min
    for cur_channel in range(num_channels):
      if (transfer_funds[cur_channel] > 0 and need_to_transfer > 0):
        channel_transfer = transfer_funds[cur_channel]
        if (channel_transfer > need_to_transfer):
          channel_transfer = need_to_transfer
        channels[cur_channel].transfer_u2o(channel_transfer)
        transfer_funds[cur_channel] -= channel_transfer
        need_to_transfer -= channel_transfer
    if (print_flag):
      self.print_user()
    else:
      self.check_user()
    self.move_from_burn(print_flag) 			# move funds from burn outputs to user's and operator's outputs in a series of single-channel updates that maintains sufficiently balanced burn amounts between the user and the operator

  def calc_largest_atomic_send(self,			# return value of largest possible atomic send given specified number of active channels
                               num_active):		# number of active channels used for atomic send
    depot = self.get_depot()
    security = depot.get_security()
    allocation = self.get_allocation()
    start_b = self.get_balance()
    u_match_factor = security.get_u_match_factor()
    o_match_factor = security.get_o_match_factor()
    channel_value = depot.get_channel_value()
    operator_channel_min = depot.get_o_channel_min()
    min_b_allowed = depot.calc_min_b(num_active)
							# limit payment size to ensure user has sufficient balance to burn payment and user's matching funds for payment
    min_b_payment_bound = math.floor(float(start_b - min_b_allowed)/(1.0 + u_match_factor))
                                                        # limit payment size to ensure user has sufficient free balance after payment
    min_b_no_burn = depot.calc_min_b_no_burn(num_active)
    min_b_no_burn_bound = start_b - min_b_no_burn
							# limit payment size to ensure operator has sufficient balance to burn operator's matching funds for payment
    operator_payment_bound = math.floor(float(num_active*(channel_value - operator_channel_min) - start_b)/o_match_factor)
                                                        # include "- 2" term due to rouding up of user's and operator's match amounts
    return min(min_b_payment_bound, min_b_no_burn_bound, operator_payment_bound) - 2

  def send(self,					# perform requested payment from user, return True iff successful
           amount,					# value of payment in 1/P-sats
           can_be_divided,				# flag indicating whether or not the payment can be divided into multiple Lightning payments, each with their own receipt
           print_flag):					# print updates if print_flag == True
    self.sends += 1
    sat_amount = amount/float(self.depot.get_prime())
    if (print_flag):
      print('***** SEND ', sat_amount, 'sats equals', amount, '1/P-sats')
    depot = self.get_depot()
    security = depot.get_security()
    allocation = self.get_allocation()
    channels = self.get_channels()
    u_channel_min = depot.get_u_channel_min()
    while (amount > 0):
      num_active = len(channels)
      start_b = self.get_balance()
							# determine if payment can be performed with current number of active channels
      payment_bound = self.calc_largest_atomic_send(num_active)
      atomic_num_active = num_active
      if (amount <= payment_bound):			# payment can be performed with current number of active channels
        atomic_amount = amount
      else: 						# payment cannot be performed with current number of active channels
        atomic_amount = payment_bound
        cur_active = num_active 			# try larger numbers of active channels
        while (cur_active <= depot.calc_max_a(start_b, allocation)):
          cur_bound = self.calc_largest_atomic_send(cur_active)
          if (cur_bound > atomic_amount):
            atomic_num_active = cur_active
            if (amount <= cur_bound):			# payment can be performed with given number of active channels
              atomic_amount = amount
              break
            else:
              atomic_amount = cur_bound
          cur_active += 1
        cur_active = num_active 			# try smaller numbers of active channels
        while (cur_active >= depot.calc_min_a(start_b, allocation) and cur_active >= self.get_min_nza()):
          cur_bound = self.calc_largest_atomic_send(cur_active)
          if (cur_bound > atomic_amount):
            atomic_num_active = cur_active
            if (amount <= cur_bound):			# payment can be performed with given number of active channels
              atomic_amount = amount
              break
            else:
              atomic_amount = cur_bound
          cur_active -= 1
      if (atomic_amount < amount and not can_be_divided):
        return False
							# get required number of active channels for first atomic payment
      if (num_active > atomic_num_active):
        need_to_revoke = num_active - atomic_num_active
        while (need_to_revoke > 0):
          need_to_revoke -= 1
          self.atomic_revoke(print_flag)
      if (num_active < atomic_num_active):
        need_to_acquire = atomic_num_active - num_active
        while (need_to_acquire > 0):
          need_to_acquire -= 1
          self.atomic_acquire(print_flag)
							# perform atomic send
      self.atomic_send(atomic_amount, print_flag)
      amount -= atomic_amount
    return True

  def drain(self,					# drain all funds and revoke all channels for given user
            print_flag):				# print updates if print_flag == True
    if (print_flag):
      print('***** DRAIN')
    self.channels = []
    if (print_flag):
      self.print_user()
    else:
      self.check_user()

  def print_stats(self):				# print send and receive stats
    print('Sends:', self.sends, 'Atomic sends:', self.atomic_sends, 'Receives:', self.receives, 'Atomic receives:', self.atomic_receives, 'Cumulative channels:', self.cumulative_channels, 'Channel updates:', self.channel_updates,\
          'Channels/payment:', float(self.cumulative_channels)/float(self.sends + self.receives), 'Updates/payment:', float(self.channel_updates)/float(self.sends + self.receives))

  def check_user(self):					# check that required invariants hold
    depot = self.depot
    allocation = self.allocation
    num_channels = self.get_num_channels()
    channels = self.channels
    balance = self.get_balance()
    if (num_channels > 0):
      if (num_channels < self.get_min_nza()):
        self.print_user()
      assert num_channels >= self.get_min_nza()
      if (balance > depot.calc_max_b(num_channels, allocation)):
        self.print_user()
      assert balance <= depot.calc_max_b(num_channels, allocation)
    for cur_channel in range(num_channels):		# check that user's balance in each channel is large enough
      if (depot.get_u_channel_min() > channels[cur_channel].get_u_balance()):
        self.print_user()
      assert depot.get_u_channel_min() <= channels[cur_channel].get_u_balance()
    for cur_channel in range(num_channels):		# check that operator's balance in each channel is large enough
      if (depot.get_o_channel_min() > channels[cur_channel].get_o_balance()):
        self.print_user()
      assert depot.get_o_channel_min() <= channels[cur_channel].get_o_balance()
    u_burn = self.get_u_burn()				# check that frac_loss_u is within the required bounds
    o_burn = self.get_o_burn()
    depot = self.get_depot()
    if (u_burn + o_burn > 0):
      min_frac_loss_u = depot.security.get_min_frac_loss_u()
      max_frac_loss_u = depot.security.get_max_frac_loss_u()
      frac_loss_u = float(u_burn)/float(u_burn + o_burn)
      if (min_frac_loss_u > frac_loss_u):
        self.print_user()
      if (frac_loss_u > max_frac_loss_u):
        self.print_user()
      assert min_frac_loss_u <= frac_loss_u
      assert frac_loss_u <= max_frac_loss_u

  def print_user(self):					# print out current state of this user
    u_burn = self.get_u_burn()
    o_burn = self.get_o_burn()
    depot = self.get_depot()
    num_channels = self.get_num_channels()
    allocation = self.get_allocation()
    channels = self.channels
    balance = self.get_balance()
    p = float(self.depot.get_prime())
    if (num_channels > 0):
      if (u_burn + o_burn > 0):
        min_frac_loss_u = depot.security.get_min_frac_loss_u()
        max_frac_loss_u = depot.security.get_max_frac_loss_u()
        frac_loss_u = float(u_burn)/float(u_burn + o_burn)
        print('min_nonzero_channels:', self.get_min_nza(), 'active:', num_channels, 'allocation:', allocation, 'min_balance:', depot.calc_min_b_no_burn(num_channels), 'user:', self.get_balance(), 'user (sats): %9.3f' % (self.get_balance()/p), 'max_balance:', depot.calc_max_b(num_channels, allocation))
        print('user burn:', u_burn, 'user burn (sats): %9.3f' % (u_burn/p), 'total burn (sats): %9.3f' % ((u_burn+o_burn)/p), 'operator burn:', o_burn, 'operator burn (sats): %9.3f' % (o_burn/p), 'min_frac_loss_u:', min_frac_loss_u,\
              'frac_loss_u:', frac_loss_u, 'max_frac_loss_u:', max_frac_loss_u, 'num_channels:', num_channels)
      else:
        print('min_nonzero_channels:', self.get_min_nza(), 'active:', num_channels, 'allocation:', allocation, 'min_balance:', depot.calc_min_b_no_burn(num_channels), 'user:', self.get_balance(), 'user (sats): %9.3f' % (self.get_balance()/p), 'max_balance:', depot.calc_max_b(num_channels, allocation))
        print('user burn:', u_burn, 'user burn (sats): %9.3f' % (u_burn/p), 'total burn (sats): %9.3f' % ((u_burn+o_burn)/p), 'operator burn:', o_burn, 'operator burn (sats): %9.3f' % (o_burn/p), 'num_channels:', num_channels)
    else:
      if (u_burn + o_burn > 0):
        frac_loss_u = float(u_burn)/float(u_burn + o_burn)
        print('min_nonzero_channels:', self.get_min_nza(), 'active:', num_channels, 'allocation:', allocation, 'user:', self.get_balance(), 'user (sats): %9.3f' % (self.get_balance()/p))
        print('user burn:', u_burn, 'user burn (sats): %9.3f' % (u_burn/p), 'total burn (sats): %9.3f' % ((u_burn+o_burn)/p), 'operator burn:', o_burn, 'operator burn (sats): %9.3f' % (o_burn/p), 'frac_loss_u:', frac_loss_u, 'num_channels:', num_channels)
      else:
        print('min_nonzero_channels:', self.get_min_nza(), 'active:', num_channels, 'allocation:', allocation, 'user:', self.get_balance(), 'user (sats): %9.3f' % (self.get_balance()/p))
        print('user burn:', u_burn, 'user burn (sats): %9.3f' % (u_burn/p), 'total burn (sats): %9.3f' % ((u_burn+o_burn)/p), 'operator burn:', o_burn, 'operator burn (sats): %9.3f' % (o_burn/p), 'num_channels:', num_channels)
    print('channels:')
    cur_channel = 0
    for channel in channels:
      cur_channel += 1
      channel.print_balances(cur_channel, False)
    cur_channel = 0
    o_balance = 0
    for channel in channels:
      cur_channel += 1
      channel.print_balances(cur_channel, True)
      o_balance += channel.get_o_balance()
    print(' ')
    if (num_channels > 0):
      assert balance <= depot.calc_max_b(num_channels, allocation)
    for cur_channel in range(num_channels):		# check that user's balance in each channel is large enough
      assert depot.get_u_channel_min() <= channels[cur_channel].get_u_balance()
    for cur_channel in range(num_channels):		# check that operator's balance in each channel is large enough
      assert depot.get_o_channel_min() <= channels[cur_channel].get_o_balance()
    u_burn = self.get_u_burn()				# check that frac_loss_u is within the required bounds
    o_burn = self.get_o_burn()
    depot = self.get_depot()
    if (u_burn + o_burn > 0):
      min_frac_loss_u = depot.security.get_min_frac_loss_u()
      max_frac_loss_u = depot.security.get_max_frac_loss_u()
      frac_loss_u = float(u_burn)/float(u_burn + o_burn)
      assert min_frac_loss_u <= frac_loss_u
      assert frac_loss_u <= max_frac_loss_u

 
# Main program
parser = argparse.ArgumentParser(description='Calculate depot parameters as a function of given parameters)')
parser.add_argument('-u', dest='gr_u', help='security against griefing by the users')
parser.add_argument('-o', dest='gr_o', help='security against griefing by the operator')
parser.add_argument('-r', dest='balance_range', default='1.5', help='minimum value of ratio max_b(au, max_au)/min_b(au) (optional with default value of 1.5)')
parser.add_argument('-n', dest='number_of_users', help='number of users using the depot (used to calculate average allocation per user)')
parser.add_argument('-a', dest='max_active_channels', help='maximum number of active channels')
parser.add_argument('-c', dest='max_cumulative_channels', help='maximum cumulative number of channels sold over the lifetime of the depot')
parser.add_argument('-s', dest='supported_user_balances', help='lower bound on value (in sats) that can be sold to users')
parser.add_argument('-e', dest='example_flag', default=False, help='if True print example sends and receives (optional with default value of False)')
parser.add_argument('-p', dest='random_payments', default='0', help='number of random payments (sends or receives) to be performed (optional with default value of 0)')
parser.add_argument('-q', dest='random_seed', default='4886173', help='seed for randomness (optional with default value of 4886173)')
parser.add_argument('-z', dest='random_allocation', default='0', help='allocation for random user (optional with default value being a random selection from 1 through 10 times the average allocation)')
parser.add_argument('-f', dest='payment_factor', default='0.0', help='factor controlling random payment sizes (random payments change balance by a factor of at most 1.0 + f)')
args = parser.parse_args()
gr_u = float(args.gr_u)
assert gr_u >= 0
gr_o = float(args.gr_o)
assert gr_o >= 0
assert gr_u*gr_o < 1
balance_range = float(args.balance_range)
assert balance_range > 1.0
number_of_users = int(args.number_of_users)
assert number_of_users > 0
max_active_channels = int(args.max_active_channels)
assert max_active_channels >= number_of_users
max_cumulative_channels = int(args.max_cumulative_channels)
assert max_cumulative_channels >= max_active_channels
supported_user_balances = int(args.supported_user_balances)
assert supported_user_balances > 0
example_flag = bool(args.example_flag)
random_payments = int(args.random_payments)
assert random_payments >= 0
random_seed = int(args.random_seed)
assert random_seed >= 0
random_allocation = int(args.random_allocation)
assert random_allocation >= 0
payment_factor = float(args.payment_factor)
assert payment_factor >= 0.0

average_allocation = math.floor(float(max_active_channels)/float(number_of_users))

security = Security(gr_u, gr_o, balance_range)
								# max user balance divided by min user balance in user's oldest channel is the largest possible value of the balance_range parameter
assert balance_range <= security.get_max_frac_loss_u()/security.get_min_frac_loss_u()

depot = Depot(security, max_active_channels, max_cumulative_channels, supported_user_balances)
max_h = depot.get_max_h()
max_utilization = depot.get_max_utilization()
depot_value = depot.get_depot_value()
prime = depot.get_prime()
p = float(depot.get_prime())
max_b = depot.get_max_b()

average_user = User(depot, average_allocation)

print('Input parameters: gr_u:', gr_u, 'gr_o:', gr_o, 'balance_range:', balance_range, 'number_of_users:', number_of_users, 'max_active_channels:', max_active_channels, 'max_cumulative_channels:', max_cumulative_channels, 'supported_user_balances:', supported_user_balances)

print('Outputs: min_frac_loss_u: %8.6f' % security.get_min_frac_loss_u(), 'max_frac_loss_u: %8.6f' % security.get_max_frac_loss_u(), 'prime:', depot.get_prime(), 'max_h: %8.6f' % depot.get_max_h())
print('u_channel_min:', depot.get_u_channel_min(), 'u_channel_min (sats): %9.3f' % (depot.get_u_channel_min()/p), 'o_channel_min:', depot.get_o_channel_min(), 'o_channel_min (sats): %9.3f' % (depot.get_o_channel_min()/p), 'targets:', depot.get_targets(), 'g:', depot.get_g())
print('max_utilization: %8.6f' % max_utilization, 'depot_value:', depot.get_depot_value(), 'payment_scale_factor: %8.6f' % security.get_payment_scale_factor(), 'u_match_factor: %8.6f' % security.get_u_match_factor(), 'o_match_factor: %8.6f' % security.get_o_match_factor())
print('min_nonzero_channels:', average_user.get_min_nza(), 'min_fund_value:', average_user.calc_min_fund(), 'min_fund_value (sats): %9.3f' %(average_user.calc_min_fund()/p))

print(' ')

print('Typical user\'s minimum and maximum balances and per-channel capacities as a function of the number of active channels:')
for au in range(1, average_allocation+1):
  sat_min_balance = depot.calc_min_b(au)/p
  sat_min_balance_no_burn = depot.calc_min_b_no_burn(au)/p
  sat_max_balance = depot.calc_max_b(au, average_allocation)/p
  sat_max_per_channel_capacity = depot.calc_max_c(au, average_allocation)/p
  print('Au: %3d' % au, 'min_balance: %11d' % depot.calc_min_b(au), 'min_balance (sats): %9.3f' % sat_min_balance, 'min_balance_no_burn: %11d' % depot.calc_min_b_no_burn(au), 'min_balance_no_burn (sats): %9.3f' % sat_min_balance_no_burn,\
        'max_balance: %11d' %depot.calc_max_b(au, average_allocation), 'max_balance (sats): %9.3f' %sat_max_balance,\
        'per_channel_capacity: %11d' %depot.calc_max_c(au, average_allocation), 'per_channel_capacity (sats): %9.3f' % sat_max_per_channel_capacity)

print(' ')

print('Assume users failing to drain maintain their maximum funds and their maximum channels')
for frac in [0.01, 0.005, 0.001, 0.0005]:			# frac fraction of users fail to drain
  h = frac*max_h						# h is expected number of hits from users failing to drain
  u_funds = max_b*frac						# funds of users failing to drain
  u_loss = u_funds - one_hit_prob(h)*max_b*prime/max_active_channels
								# all users funds are lost except those that are paid back due to exactly one hit
  on_chain_tx = zero_hit_prob(h)*ZERO_HITS_ON_CHAIN_TX + one_hit_prob(h)*ONE_HIT_ON_CHAIN_TX + burn_prob(h)*TWO_PLUS_HITS_ON_CHAIN_TX
								# expected number of on_chain transactions
  o_loss = (depot_value*burn_prob(h)-u_loss)
  o_loss_fraction = o_loss/depot_value
  print('Active failure to drain fraction: %6.4f' % frac, 'h: %8.6f' % h, 'one_hit_prob: %8.6f' % one_hit_prob(h), 'burn prob: %8.6f' % burn_prob(h), 'user funds (sats): %12.3f' % u_funds, 'user_loss (sats): %12.3f' % u_loss, 'operator_loss (sats): %12.3f' % o_loss,\
        'operator_loss_fraction: %8.6f' % o_loss_fraction, 'on_chain_tx: %5.3f' % on_chain_tx)

print(' ')

print('Assume users failing to drain maintain half their maximum funds and half their maximum channels')
for frac in [0.01, 0.005, 0.001, 0.0005]:			# frac fraction of users fail to drain
  h = frac*max_h/2.0						# h is expected number of hits from users failing to drain
  u_funds = max_b*frac/2.0					# funds of users failing to drain
  u_loss = u_funds - one_hit_prob(h)*max_b*prime/max_active_channels
								# all users funds are lost except those that are paid back due to exactly one hit
  on_chain_tx = zero_hit_prob(h)*ZERO_HITS_ON_CHAIN_TX + one_hit_prob(h)*ONE_HIT_ON_CHAIN_TX + burn_prob(h)*TWO_PLUS_HITS_ON_CHAIN_TX
								# expected number of on_chain transactions
  o_loss = (depot_value*burn_prob(h)-u_loss)
  o_loss_fraction = o_loss/depot_value
  print('Active failure to drain fraction: %6.4f' % frac, 'h: %8.6f' % h, 'one_hit_prob: %8.6f' % one_hit_prob(h), 'burn prob: %8.6f' % burn_prob(h), 'user funds (sats): %12.3f' % u_funds, 'user_loss (sats): %12.3f' % u_loss, 'operator_loss (sats): %12.3f' % o_loss,\
        'operator_loss_fraction: %8.6f' % o_loss_fraction, 'on_chain_tx: %5.3f' % on_chain_tx)

print(' ')

if (example_flag):
  print('Average user initial state:')
  average_user.print_user()
  assert average_user.calc_min_fund() <= 55*prime
  average_user.fund(55*prime, True)				# fund average_user with 55 sats
  average_user.receive(5*prime, True, True)			# send 5 sats to average_user, resulting in a 60-sat balance
  assert average_user.calc_min_fund() <= 50*prime
  average_user.send(10*prime, True, True)			# send 10 sats from average_user, resulting in a 50-sat balance
  average_user.receive(30*prime, True, True)			# send 30 sats to average_user, resulting in an 80-sat balance
  average_user.send(25*prime, True, True)			# send 25 sats from average_user, resulting in a 55-sat balance
  assert average_user.calc_min_fund() <= 25*prime
  average_user.send(30*prime, True, True)			# send 30 sats from average_user, resulting in a 25-sat balance
  average_user.drain(True)					# drain average_user, resulting in a 0-sat balance
  average_user.print_stats()

if (random_payments > 0):
  random.seed(random_seed)
  if (random_allocation == 0):
    random_allocation = random.randint(1, int(10*average_allocation))
  random_user = User(depot, random_allocation)
  min_balance_no_burn = random_user.calc_min_fund()
  max_balance = depot.calc_max_b(random_allocation, random_allocation)
  print(' ')

  print('Random user\'s minimum and maximum balances and per-channel capacities as a function of the number of active channels:')
  for au in range(1, random_allocation+1):
    sat_min_balance = depot.calc_min_b(au)/p
    sat_min_balance_no_burn = depot.calc_min_b_no_burn(au)/p
    sat_max_balance = depot.calc_max_b(au, random_allocation)/p
    sat_max_per_channel_capacity = depot.calc_max_c(au, random_allocation)/p
    print('Au: %3d' % au, 'min_balance: %11d' % depot.calc_min_b(au), 'min_balance (sats): %9.3f' % sat_min_balance, 'min_balance_no_burn: %11d' % depot.calc_min_b_no_burn(au), 'min_balance_no_burn (sats): %9.3f' % sat_min_balance_no_burn,\
          'max_balance: %11d' %depot.calc_max_b(au, random_allocation), 'max_balance (sats): %9.3f' %sat_max_balance,\
          'per_channel_capacity: %11d' %depot.calc_max_c(au, random_allocation), 'per_channel_capacity (sats): %9.3f' % sat_max_per_channel_capacity)

  print(' ')
  print('Random user:')
  sat_min_balance_no_burn = min_balance_no_burn/p
  sat_max_balance = max_balance/p
  print('min_nonzero_channels:', random_user.get_min_nza(), 'min_balance_no_burn (sats): %9.3f' % sat_min_balance_no_burn, 'max_balance (sats): %9.3f' % sat_max_balance)
  random_user.print_user()
  random_balance = random.randint(min_balance_no_burn, max_balance)
  random_user.fund(int(random_balance), True)
  for i in range(random_payments):
    if (payment_factor == 0.0):
      new_balance = random.randint(min_balance_no_burn, max_balance)
    else:
      low_bound = max(min_balance_no_burn, math.ceil(random_balance/(1.0 + payment_factor)))
      high_bound = min(max_balance, math.floor(random_balance*(1.0 + payment_factor)))
      new_balance = random.randint(low_bound, high_bound)
    print_flag = (i % max(1, int(random_payments/10)) == 0)
    if (print_flag):
      print('Random payment #:', i, 'balance:', random_balance, 'sat_balance:', random_balance/p, 'new_balance:', new_balance, 'sat_new_balance:', new_balance/p)
    if (new_balance >= random_balance):
      random_user.receive(new_balance - random_balance, True, print_flag)
    else:
      random_user.send(random_balance - new_balance, True, print_flag)
    random_balance = new_balance
  random_user.drain(True)
  random_user.print_stats()

