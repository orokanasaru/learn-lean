import { Message } from '@bryangingechen/lean-client-js-browser';
import React, { useEffect, useState } from 'react';
import { leanColorize } from '.';

interface MessageWidgetProps {
  msg: Message;
}

export function MessageWidget({ msg }: MessageWidgetProps) {
  const [text, setText] = useState(msg.text);

  useEffect(() => {
    leanColorize(text).then(setText);
  }, [msg.text]);

  const colorOfSeverity = {
    information: 'green',
    warning: 'orange',
    error: 'red',
  };

  // TODO: links and decorations on hover
  return (
    <div style={{ paddingBottom: '1em' }}>
      <div
        className='info-header'
        style={{ color: colorOfSeverity[msg.severity] }}
      >
        {msg.pos_line}:{msg.pos_col}: {msg.severity}: {msg.caption}
      </div>
      <div className='code-block' dangerouslySetInnerHTML={{ __html: text }} />
    </div>
  );
}
