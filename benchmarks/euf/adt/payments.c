/* @KESTREL
 * pre: left.ids_in == right.ids_in
     && left.salaries_in == right.salaries_in
     && left.num_updates_in == right.num_updates_in
     && left.payments_in == right.payments_in;
 * left: left;
 * right: right;
 * post: left.payments == right.payments;
 */

// A mutating method payments.method(args) is modeled as:
// payments = method(payments, args)

int send_paycheck(int payments, int id, int amount);
int yearly_bonus(int year);
int read(int list, int index);

void _test_gen(int payments, int ids, int salaries, int num_updates) {
  if (num_updates < 0) { num_updates = num_updates * -1; }
  num_updates = num_updates % 100;
  _main(payments, ids, salaries, num_updates, payments, ids, salaries, num_updates);
}

void left(int payments_in, int ids_in, int salaries_in, int num_updates_in) {
  int payments = payments_in;
  int ids = ids_in;
  int salaries = salaries_in;
  int num_updates = num_updates_in;

  int i = 0;
  while (i < num_updates) {
    int id = read(ids, i);
    int salary = read(salaries, i);
    int bonus = yearly_bonus(2024);
    payments = send_paycheck(payments, id, salary + bonus);
    i = i + 1;
  }
}

void right(int payments_in, int ids_in, int salaries_in, int num_updates_in) {
  int payments = payments_in;
  int ids = ids_in;
  int salaries = salaries_in;
  int num_updates = num_updates_in;

  int bonus = yearly_bonus(2024);
  int i = 0;
  while (i < num_updates) {
    int id = read(ids, i);
    int salary = read(salaries, i);
    payments = send_paycheck(payments, id, salary + bonus);
    i = i + 1;
  }
}
