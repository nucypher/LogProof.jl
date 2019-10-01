struct IOChannel
    input :: Channel
    output :: Channel

    IOChannel() = new(Channel(0), Channel(0))
    IOChannel(c::IOChannel) = new(c.output, c.input)
end


Base.put!(c::IOChannel, val) = put!(c.output, val)


Base.take!(c::IOChannel) = take!(c.input)


function task_wrapper(func, args...)
    try
        func(args...)
    catch err
        bt = catch_backtrace()
        showerror(stderr, err, bt)
        println()
        rethrow()
    end
end


function run_pair(task1, task2, task1_args, task2_args)
    c1 = IOChannel()
    c2 = IOChannel(c1)
    #t1 = @task task1(c1, task1_args...)
    #t2 = @task task2(c2, task2_args...)

    t1 = @task task_wrapper(task1, c1, task1_args...)
    t2 = @task task_wrapper(task2, c2, task2_args...)
    schedule(t1)
    schedule(t2)
    yield()
    r1 = fetch(t1)
    r2 = fetch(t2)
    r1, r2
end
