---
layout: post
title:  "Hooks bring React closer to Functional Reactive Programming"
date:   2018-02-22 00:30:00
categories: 
---

React recently got hooks, which allows you to use function components even if you need behaviour such as state, which required class components in previous versions. This is the example from the React website:

{% highlight jsx %}
function Example() {
  // Declare a new state variable, which we'll call "count"
  const [count, setCount] = useState(0);

  return (
    <div>
      <p>You clicked {count} times</p>
      <button onClick={() => setCount(count + 1)}>
        Click me
      </button>
    </div>
  );
}
{% endhighlight %}

I know nothing about React, so take this post with a big grain of salt, but this reminded me of old FRP systems such as [FranTk](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.25.8446&rep=rep1&type=pdf). The analogue to `useState(x)` is called `newBVar x`, which returns a BVar -- essentially an abstraction around the [count,setCount] pair. Hooks allow React components to be written in a style similar to FRP.

There is one big difference between React and FRP. The variable `count` in the React example is a plain old number, and React manages the updating of the component through magic behind the scenes. FRP wraps this value in a container that represents a value that changes in time. This means that FRP code cannot operate on values directly. Instead of `count + 1` you must write `count.map(x => x+1)`. Functions such as `map` set up a dataflow network so that the FRP system can propagate changes in a fine grained manner. Besides the obvious disadvantage, this does have the advantage of being conceptually clearer and more general. React has certain restrictions on where and how you can call `useState`, whereas FRP systems have no such restrictions. The change tracking will correctly track BVars that are created conditionally, and it will only update exactly the parts of a component that are affected by a change, rather than re-rendering the entire component.

The idiomatic way to write components in FranTk style FRP is to pass BVars *into* functions. For instance, a reusable counter would look something like the following:

{% highlight javascript %}
function Counter(state) {
  const [count, setCount] = state;

  return (
    <div>
      <p>You clicked {count} times</p>
      <button onClick={() => setCount(count + 1)}>
        Click me
      </button>
    </div>
  );
}
{% endhighlight %}

A new counter is created with `state = useState(0); Counter(state)`. This allows the enclosing component to read and write the counter state. In a todolist application like the TodoMVC example application you might have a `TodoItem(todoItemState)` component, which takes a `todoItemState = [todoItem, setTodoItem]` as an argument, where `todoItem` consists of the todo text and the boolean indicating whether the todo item has been completed. The `TodoItem` component will create the textbox and checkbox, and will call `setTodoItem` to update the state when the user types in the textbox or toggles the checkbox. You may agree that it makes sense to consider `[foo, setFoo]` as a single `BVar`, rather than two separate things. If nothing else, it may help to have a name for such pairs of a state and setter function.

The general pattern is that a component takes its externally visible state as an argument, and allocates new BVars/useStates for encapsulated state or UI state. For instance, a `TodoList` component would take the todo list state an an argument (containing a list of todo items). The UI state that determines whether to show or hide completed todo items would be encapsulated, so the `TodoList` component would have an internal `useState` for that:

{% highlight javascript %}
function TodoList(todoListState) {
  const [todoList, setTodoList] = todoliststate;
  const [showCompleted, setShowCompleted] = useState(true);

  return (
    <div>
      ...
      <Checkbox value={showCompleted} onchange={setShowCompleted}>
    </div>
  );
}
{% endhighlight %}

Considering the pair `[showCompleted, setShowCompleted]` as a thing of its own can lead to simplications, e.g. a `Checkbox` component that understands that pair:

{% highlight javascript %}
function TodoList(todoListState) {
  const [todoList, setTodoList] = todoliststate;
  const showCompletedState = useState(true);

  return (
    <div>
      ...
      <Checkbox state={showCompletedState} />
    </div>
  );
}
{% endhighlight %}

Some years ago I wrote a toy FRP wrapper around PyQt with the aim of enabling this idiom. It's surprising how little you actually need: just a BVar that tracks dependencies in the dataflow network and change listeners that get called whenever a BVar changes. With just 100 lines of code or so you can write UIs in a pleasant style, if you're willing to put up with the FRP annoyance of having to write `map` everywhere.