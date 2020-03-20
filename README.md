# TLA-Plus-Learning
An unorganized collection of TLA+ samples.

These samples follow this [tutorial by Hillel Wayne](https://learntla.com/introduction/).

## First of All, What is TLA+?
TLA+ is a formal specification language. Think of TLA+ as blueprints for software engineering.

## Why should I care about TLA+?
Essentially, TLA+ can be used to model every possible state your system can be in. If used properly, you can show where invariants in your system fail. While this won't make your actualy software correct, you can use it as a map to guide your actual code.

Furthermore, you can use TLA+ to model concurrent systems and find where deadlock can occur in your design. If you're going to design a system properly, I strongly suggest you use TLA+ to assist you. Would you want to go inside a building that didn't abide by a blueprint? If not, then why would you want to trust a system that didn't abide by a proper specification?

## How do I run the TLA+ files here?
I use the [TLA Toolbox](http://lamport.azurewebsites.net/tla/toolbox.html). Click [here](https://github.com/tlaplus/tlaplus/releases/tag/v1.6.0) for the download link. I won't go into great detail about how to run the files themselves. The links I've provided thoroughly document this.

I do want to emphasize that the IDE is extremely helpful because you can specify models that you can run your TLA+ code against to see if your spec holds.
