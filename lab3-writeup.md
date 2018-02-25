2.a. (const x = 5; const x = 4; x + 5) + x
Under dynamic scoping this test would return 13 because x was last initialized
as 4, but under static scoping this test would return 14. This is because that
last reference to x was 4 in dynamic scoping, but in static scoping it was 5.


3.d. Yes this evaluation order is deterministic because the judgment form
specifies the step that e takes to get to e'. This step will always be the same
in this specific judgment form where as in big step you can pass the expression
to be evaluated but it is not guaranteed the same process will occur each time.

4. The evaluation order is e1 first then e2. 
So e1 will be evaluated to a value then e2 will be evaluated to a value.
Then they will be added together. 
To evaluate in the opposite order you would need to evaluate e2 to a value first,
then evaluate e1 to a value, then compute the addtition between the two.

5.a. Consider the situation where you have v1 && e2, where e2 was a
large expression that requires many steps to evaluate. If v1 was B(false)
the entire expression that was v1 && e2 would just evaluate to the value
B(false), and e2 would not be required to be evaluated. This saves time.

b. No e1 && e2 does not short circuit because e1 is not a value and must be
stepped on until it becomes a value. Only v1 && e2 will short circuit given
toBoolean(v1) is B(false).